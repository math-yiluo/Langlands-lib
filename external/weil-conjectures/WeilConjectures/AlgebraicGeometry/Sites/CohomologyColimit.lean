/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import Mathlib.AlgebraicGeometry.Cover.QuasiCompact
public import Mathlib.CategoryTheory.Sites.EpiMono
public import WeilConjectures.AlgebraicGeometry.Sites.PointFunctions
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients
public import WeilConjectures.CategoryTheory.Sites.CechCriterion
public import WeilConjectures.Mathlib.Algebra.Category.Grp.Colimits
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.ConstructibleSheaf.FreeLifting

/-!
# Étale cohomology of a direct sum on a quasi-compact quasi-separated scheme

On a quasi-compact and quasi-separated scheme `X`, étale cohomology commutes with filtered
colimits of abelian sheaves ([Stacks 03Q6]), and hence with direct sums, a direct sum being the
filtered colimit of its finite partial sums. We record the consequence used for the divisor
sequence: a direct sum of sheaves without cohomology in degree `n` has no cohomology in degree
`n`.

## Main statements

- `AlgebraicGeometry.Scheme.exists_cofanFinsetDesc_app_eq`: over an étale `X`-scheme with
  quasi-compact underlying space, every section of `⨁ᵢ Fᵢ` comes from a finite partial sum.
- `AlgebraicGeometry.Scheme.subsingleton_H_one_of_isColimit_cofan`: on a quasi-compact
  quasi-separated scheme, if `H¹(X, Fᵢ) = 0` for all `i`, then `H¹(X, ⨁ᵢ Fᵢ) = 0`.
- `AlgebraicGeometry.Scheme.subsingleton_H_succ_of_isColimit_cofan_of_injective`: on a
  quasi-compact quasi-separated scheme, a direct sum of injective sheaves has no higher
  cohomology.
- `AlgebraicGeometry.Scheme.subsingleton_H_of_isColimit_cofan`: if `Hⁿ(X, Fᵢ) = 0` for all `i`,
  then `Hⁿ(X, ⨁ᵢ Fᵢ) = 0`, in every degree `n`.

## Implementation notes

In degree one we argue with lifts of global sections instead of filtered colimits. Let
`0 → ⨁ᵢ Fᵢ → E → Q → 0` be exact and `q` a global section of `Q`. It lifts to sections `e_a` of
`E` on a finite family of affine étale `X`-schemes `U_a` covering `X`. The differences of the
`e_a` on the quasi-compact overlaps `U_a ×_X U_b` are sections of `⨁ᵢ Fᵢ`, hence locally finite
sums, and finitely many indices `S` suffice for all of them. Modulo the finite sum
`G = ⨁_{i ∈ S} Fᵢ` the `e_a` glue, and as `H¹(G) = 0` the glued section lifts to `E`.

For a direct sum of injective sheaves `Iᵢ` we use the Čech criterion
`CategoryTheory.Sheaf.subsingleton_H_succ_of_exactAt_cechComplex` on the étale `X`-schemes with
quasi-compact quasi-separated underlying scheme: a Čech cochain of `⨁ᵢ Iᵢ` on a finite family of
such schemes comes from a finite partial sum, which is injective, so its Čech complexes are
exact in positive degrees. The general case follows by dimension shifting along
`0 → ⨁ Fᵢ → ⨁ Iᵢ → ⨁ Qᵢ → 0`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}}

/-- On an étale `X`-scheme `W` with quasi-compact underlying space, every covering sieve
contains a finite jointly surjective family of étale `X`-schemes with affine underlying
schemes. -/
lemma exists_finite_affine_of_mem_smallEtaleTopology {W : X.Etale} [CompactSpace W.left]
    {R : Sieve W} (hR : R ∈ X.smallEtaleTopology W) :
    ∃ (n : ℕ) (U : Fin n → X.Etale) (g : ∀ a, U a ⟶ W), (∀ a, R (g a)) ∧
      (∀ a, IsAffine (U a).left) ∧ ⋃ a, Set.range (g a).left = Set.univ :=
  AlgebraicGeometry.Etale.exists_affine_refinement.{u} R hR

/-- A jointly surjective family of morphisms of étale `X`-schemes is a covering family for
every abelian étale sheaf. -/
lemma isSheafFor_ofArrows (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) {W : X.Etale}
    {κ : Type*} {U : κ → X.Etale} (g : ∀ a, U a ⟶ W)
    (hg : ⋃ a, Set.range (g a).left = Set.univ) :
    Presieve.IsSheafFor (F.obj ⋙ CategoryTheory.forget _) (Presieve.ofArrows U g) := by
  have := (isSheaf_iff_isSheaf_of_type _ _).mp
    (Presheaf.isSheaf_comp_of_isSheaf _ F.obj (CategoryTheory.forget AddCommGrpCat) F.property)
  rw [Presieve.isSheafFor_iff_generate]
  exact this _ ((ofArrows_mem_smallEtaleTopology_iff g).2 hg)

/-- **Sections of a direct sum are locally finite sums.** Let `c` be a coproduct of a family
`F` of abelian étale sheaves on `X`. Every section of `c.pt` over `W` is, on the members of a
covering sieve of `W`, a finite sum of sections coming from the `Fᵢ`. -/
lemma exists_mem_forall_eq_sum_of_isColimit_cofan {ι : Type u}
    {F : ι → Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}} {c : Cofan F} (hc : IsColimit c)
    {W : X.Etale} (s : c.pt.obj.obj (op W)) :
    ∃ R ∈ X.smallEtaleTopology W, ∀ ⦃V : X.Etale⦄ (f : V ⟶ W), R f →
      ∃ (T : Finset ι) (a : ∀ i, (F i).obj.obj (op V)),
        c.pt.obj.map f.op s = ∑ i ∈ T, (c.inj i).hom.app (op V) (a i) := by
  let P := ∐ fun i ↦ (F i).obj
  let φ : P ⟶ c.pt.obj := Sigma.desc fun i ↦ (c.inj i).hom
  -- `φ` factors through the sheafification of `P` by an epimorphism of sheaves
  let ψ : (presheafToSheaf _ _).obj P ⟶ c.pt :=
    ⟨sheafifyLift X.smallEtaleTopology φ c.pt.property⟩
  have hφ : φ = toSheafify X.smallEtaleTopology P ≫ ψ.hom :=
    (toSheafify_sheafifyLift _ _ _).symm
  have hψ : Epi ψ := by
    refine ⟨fun {Z} g h hgh ↦ Cofan.IsColimit.hom_ext hc _ _ fun i ↦ ?_⟩
    have e : c.inj i = (⟨Sigma.ι (fun i ↦ (F i).obj) i ≫ toSheafify _ P⟩ :
        F i ⟶ (presheafToSheaf _ _).obj P) ≫ ψ := by
      ext1
      change _ = Sigma.ι (fun i ↦ (F i).obj) i ≫ toSheafify _ P ≫ ψ.hom
      rw [← hφ, Sigma.ι_comp_desc]
    rw [e, Category.assoc, Category.assoc, hgh]
  have := (Sheaf.isLocallySurjective_iff_epi' (A := AddCommGrpCat.{u + 1}) ψ).2 hψ
  have : Presheaf.IsLocallySurjective X.smallEtaleTopology φ := by
    rw [hφ]
    infer_instance
  refine ⟨_, Presheaf.imageSieve_mem _ φ s, fun V f ⟨p, hp⟩ ↦ ?_⟩
  have hP := isColimitCofanMkObjOfIsColimit ((CategoryTheory.evaluation _ _).obj (op V)) _
    (Sigma.ι fun i ↦ (F i).obj) (coproductIsCoproduct _)
  obtain ⟨T, a, rfl⟩ := AddCommGrpCat.exists_eq_sum_of_isColimit_cofan hP p
  refine ⟨T, a, hp.symm.trans ?_⟩
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  change (Sigma.ι (fun i ↦ (F i).obj) i ≫ φ).app (op V) (a i) = _
  rw [Sigma.ι_comp_desc]

variable (X) in
/-- **`H¹` commutes with direct sums on a qcqs scheme.** Let `X` be quasi-compact and
quasi-separated and let `c` be a coproduct of a family `F` of abelian étale sheaves on `X`. If
`H¹(X, Fᵢ) = 0` for all `i`, then `H¹(X, c.pt) = 0`. -/
theorem subsingleton_H_one_of_isColimit_cofan [CompactSpace X] [QuasiSeparatedSpace X]
    {ι : Type u} {F : ι → Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}} {c : Cofan F}
    (hc : IsColimit c) (hF : ∀ i, Subsingleton (Sheaf.H (F i) 1)) :
    Subsingleton (Sheaf.H c.pt 1) := by
  classical
  let T : X.Etale := Etale.mk (𝟙 X)
  have hT : IsTerminal T := MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale _
  refine Sheaf.subsingleton_H_one_of_surjective _ hT fun E Q ι' π w hS q ↦ ?_
  have := hS.mono_f
  have (U : X.Etaleᵒᵖ) : PreservesLimits
      ((sheafSections X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj U) :=
    inferInstanceAs (PreservesLimits (sheafToPresheaf _ _ ⋙ (CategoryTheory.evaluation _ _).obj U))
  have hexact (U) (x : E.obj.obj U) (hx : π.hom.app U x = 0) : ∃ g, ι'.hom.app U g = x :=
    (ShortComplex.ab_exact_iff _).1 (hS.exact.map_of_mono_of_preservesKernel
      ((sheafSections X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj U) hS.mono_f
      inferInstance) x hx
  have := hS.epi_g
  have := (Sheaf.isLocallySurjective_iff_epi' (A := AddCommGrpCat.{u + 1}) π).2 inferInstance
  -- Step 1: `q` lifts on finitely many affine étale `X`-schemes covering `X`
  have : CompactSpace T.left := ‹CompactSpace X›
  obtain ⟨n, U, g, hR, hU, hcov⟩ := (AlgebraicGeometry.Etale.exists_affine_refinement _)
    (Presheaf.imageSieve_mem X.smallEtaleTopology π.hom (U := op T) q)
  choose e he using hR
  -- Step 2: the differences on the overlaps are sections of `c.pt`
  have hW (a b : Fin n) : CompactSpace (pullback (g a) (g b)).left := by
    let iso := PreservesPullback.iso (Etale.forget X ⋙ Over.forget X) (g a) (g b)
    have : IsAffine (U a).left := hU a
    have : IsAffine (U b).left := hU b
    have : QuasiCompact (g b).left :=
      @quasiCompact_of_compactSpace _ _ (g b).left inferInstance ‹QuasiSeparatedSpace X›
    have : CompactSpace ↥(Limits.pullback (C := Scheme.{u}) (g a).left (g b).left) :=
      inferInstance
    exact @Homeomorph.compactSpace _ _ _ _ this
      (TopCat.homeoOfIso (Scheme.forgetToTop.mapIso iso).symm)
  have hd (a b : Fin n) : π.hom.app _ (E.obj.map (pullback.fst (g a) (g b)).op (e a) -
      E.obj.map (pullback.snd (g a) (g b)).op (e b)) = 0 := by
    rw [map_sub, NatTrans.naturality_apply, NatTrans.naturality_apply, he, he,
      ← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← Functor.map_comp,
      ← Functor.map_comp, ← op_comp, ← op_comp, pullback.condition, sub_self]
  choose γ hγ using fun a b ↦ hexact _ _ (hd a b)
  -- Step 3: locally on the overlaps, these are finite sums
  have hfin (a b : Fin n) : ∃ (S : Finset ι) (m : ℕ) (V : Fin m → X.Etale)
      (h : ∀ k, V k ⟶ pullback (g a) (g b)), (⋃ k, Set.range (h k).left = Set.univ) ∧
      ∀ k, ∃ x : ∀ i, (F i).obj.obj (op (V k)),
        c.pt.obj.map (h k).op (γ a b) = ∑ i ∈ S, (c.inj i).hom.app _ (x i) := by
    obtain ⟨R, hR, hsum⟩ := exists_mem_forall_eq_sum_of_isColimit_cofan hc (γ a b)
    obtain ⟨m, V, h, hRh, -, hcov⟩ := (AlgebraicGeometry.Etale.exists_affine_refinement _) hR
    choose S x hx using fun k ↦ hsum (h k) (hRh k)
    refine ⟨Finset.univ.biUnion S, m, V, h, hcov, fun k ↦
      ⟨fun i ↦ if i ∈ S k then x k i else 0, ?_⟩⟩
    rw [hx k]
    symm
    rw [← Finset.sum_subset (Finset.subset_biUnion_of_mem S (Finset.mem_univ k))]
    · exact Finset.sum_congr rfl fun i hi ↦ by simp [hi]
    · intro i _ hi
      simp [hi]
  choose S m V h hVcov x hx using hfin
  -- Step 4: the finite sum `G = ⨁_{i ∈ S₀} Fᵢ` of all indices needed
  let S₀ : Finset ι := Finset.univ.biUnion fun ab : Fin n × Fin n ↦ S ab.1 ab.2
  have hS₀ (a b : Fin n) : S a b ⊆ S₀ :=
    Finset.subset_biUnion_of_mem (fun ab : Fin n × Fin n ↦ S ab.1 ab.2) (Finset.mem_univ (a, b))
  let F' : S₀ → Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} := fun i ↦ F i.1
  have : HasFiniteBiproducts (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
    Abelian.hasFiniteBiproducts
  let j : ⨁ F' ⟶ c.pt := biproduct.desc fun i ↦ c.inj i.1
  have hj (i : ι) (hi : i ∈ S₀) : c.inj i = biproduct.ι F' ⟨i, hi⟩ ≫ j := by simp [j]
  have : Mono j := by
    let r : c.pt ⟶ ⨁ F' :=
      Cofan.IsColimit.desc hc fun i ↦ if hi : i ∈ S₀ then biproduct.ι F' ⟨i, hi⟩ else 0
    refine SplitMono.mono ⟨r, biproduct.hom_ext' _ _ fun i ↦ ?_⟩
    simp [j, r, Cofan.IsColimit.fac, i.2]
  have hG : Subsingleton (Sheaf.H (⨁ F') 1) :=
    have (i : S₀) : Subsingleton (Sheaf.H (F' i) 1) := hF i.1
    (Abelian.Ext.addEquivBiproduct _ (biproduct.isBilimit F') 1).toEquiv.subsingleton
  let ρ := cokernel.π (j ≫ ι')
  have hSρ : (ShortComplex.mk (j ≫ ι') ρ (cokernel.condition _)).ShortExact :=
    ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel _) inferInstance inferInstance
  have hρ (i : ι) (hi : i ∈ S₀) (V : X.Etaleᵒᵖ) (y : (F i).obj.obj V) :
      ρ.hom.app V (ι'.hom.app V ((c.inj i).hom.app V y)) = 0 := by
    have : c.inj i ≫ ι' ≫ ρ = 0 := by
      rw [hj i hi, Category.assoc, ← Category.assoc j, cokernel.condition, comp_zero]
    exact congrArg (fun φ ↦ φ.hom.app V y) this
  -- Step 5: modulo `G` the lifts `e_a` glue
  have hzero (a b : Fin n) : ρ.hom.app _ (ι'.hom.app _ (γ a b)) = 0 := by
    refine (isSheafFor_ofArrows (cokernel (j ≫ ι')) (h a b) (hVcov a b)).isSeparatedFor.ext
      fun Z f ⟨k⟩ ↦ ?_
    change (cokernel (j ≫ ι')).obj.map _ _ = (cokernel (j ≫ ι')).obj.map _ 0
    rw [map_zero, ← NatTrans.naturality_apply, ← NatTrans.naturality_apply, hx, map_sum,
      map_sum]
    exact Finset.sum_eq_zero fun i hi ↦ hρ i (hS₀ a b hi) _ _
  obtain ⟨y, hy, -⟩ := ((Presieve.isSheafFor_arrows_iff_pullbacks _ g).1
    (isSheafFor_ofArrows (cokernel (j ≫ ι')) g hcov)) (fun a ↦ ρ.hom.app _ (e a)) fun a b ↦ by
      change (cokernel (j ≫ ι')).obj.map _ _ = (cokernel (j ≫ ι')).obj.map _ _
      rw [← NatTrans.naturality_apply, ← NatTrans.naturality_apply, ← sub_eq_zero, ← map_sub,
        ← hγ, hzero]
  -- Step 6: the glued section lifts to `E`, as `H¹(G) = 0`
  obtain ⟨x₀, hx₀⟩ : y ∈ (ρ.hom.app (op T)).hom.range := by
    rw [← Sheaf.H.ker_δ hSρ hT]
    exact Subsingleton.elim (h := hG) _ _
  refine ⟨x₀, ?_⟩
  -- Step 7: and the lift maps to `q`
  let τ : cokernel (j ≫ ι') ⟶ Q := cokernel.desc _ π (by simp [w])
  have hτ : ρ ≫ τ = π := cokernel.π_desc _ _ _
  refine (isSheafFor_ofArrows Q g hcov).isSeparatedFor.ext fun Z f ⟨a⟩ ↦ ?_
  have hτx : π.hom.app _ x₀ = τ.hom.app _ y := by
    rw [← hx₀, ← hτ]
    rfl
  change Q.obj.map _ (π.hom.app _ x₀) = Q.obj.map _ _
  rw [hτx, ← NatTrans.naturality_apply]
  erw [hy a]
  rw [← he, ← hτ]
  rfl

section FiniteSum

variable {ι : Type u} {F : ι → Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}} (c : Cofan F)

instance : HasFiniteBiproducts (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
  Abelian.hasFiniteBiproducts

/-- For a finite set `S` of indices, the morphism `⨁_{i ∈ S} Fᵢ ⟶ c.pt` to a coproduct. -/
noncomputable def cofanFinsetDesc (S : Finset ι) : (⨁ fun i : S ↦ F i.1) ⟶ c.pt :=
  biproduct.desc fun i ↦ c.inj i.1

@[reassoc (attr := simp)]
lemma ι_cofanFinsetDesc (S : Finset ι) (i : S) :
    biproduct.ι (fun i : S ↦ F i.1) i ≫ cofanFinsetDesc c S = c.inj i.1 := by
  simp [cofanFinsetDesc]

variable {c}

/-- The morphism `⨁_{i ∈ S} Fᵢ ⟶ c.pt` is a split monomorphism. -/
lemma cofanFinsetDesc_comp_desc [DecidableEq ι] (hc : IsColimit c) (S : Finset ι) :
    cofanFinsetDesc c S ≫ Cofan.IsColimit.desc hc
      (fun i ↦ if hi : i ∈ S then biproduct.ι (fun i : S ↦ F i.1) ⟨i, hi⟩ else 0) = 𝟙 _ := by
  refine biproduct.hom_ext' _ _ fun i ↦ ?_
  simp [Cofan.IsColimit.fac]

/-- The morphism `⨁_{i ∈ S} Fᵢ ⟶ c.pt` is injective on sections. -/
lemma injective_cofanFinsetDesc_app (hc : IsColimit c) (S : Finset ι) (W : X.Etaleᵒᵖ) :
    Function.Injective ((cofanFinsetDesc c S).hom.app W) := fun a b h ↦ by
  classical
  have := congrArg ((Cofan.IsColimit.desc hc
    (fun i ↦ if hi : i ∈ S then biproduct.ι (fun i : S ↦ F i.1) ⟨i, hi⟩ else 0)).hom.app W) h
  rwa [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← NatTrans.comp_app,
    ← ObjectProperty.FullSubcategory.comp_hom, cofanFinsetDesc_comp_desc,
    ObjectProperty.FullSubcategory.id_hom, NatTrans.id_app] at this

/-- A finite sum of sections of the `Fᵢ` in `c.pt` comes from `⨁_{i ∈ S} Fᵢ`. -/
lemma sum_eq_cofanFinsetDesc_app (S : Finset ι) (W : X.Etaleᵒᵖ) (x : ∀ i, (F i).obj.obj W) :
    ∑ i ∈ S, (c.inj i).hom.app W (x i) = (cofanFinsetDesc c S).hom.app W
      (∑ i : S, (biproduct.ι (fun i : S ↦ F i.1) i).hom.app W (x i)) := by
  rw [map_sum, ← Finset.sum_coe_sort S]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [← ConcreteCategory.comp_apply, ← NatTrans.comp_app,
    ← ObjectProperty.FullSubcategory.comp_hom, ι_cofanFinsetDesc]

/-- For `S ⊆ S'`, the morphism `⨁_{i ∈ S} Fᵢ ⟶ c.pt` factors through `⨁_{i ∈ S'} Fᵢ`. -/
lemma cofanFinsetDesc_eq_comp {S S' : Finset ι} (h : S ⊆ S') :
    cofanFinsetDesc c S = biproduct.desc (fun i : S ↦
      biproduct.ι (fun i : S' ↦ F i.1) ⟨i.1, h i.2⟩) ≫ cofanFinsetDesc c S' := by
  refine biproduct.hom_ext' _ _ fun i ↦ ?_
  simp


/-- **Sections of a direct sum over a quasi-compact étale `X`-scheme are finite sums.** Let `c`
be a coproduct of abelian étale sheaves `Fᵢ` on `X` and `W` an étale `X`-scheme with
quasi-compact underlying space. Every section of `c.pt` over `W` comes from `⨁_{i ∈ S} Fᵢ` for
a finite set `S` of indices. -/
lemma exists_cofanFinsetDesc_app_eq (hc : IsColimit c) {W : X.Etale} [CompactSpace W.left]
    (s : c.pt.obj.obj (op W)) :
    ∃ (S : Finset ι) (y : (⨁ fun i : S ↦ F i.1).obj.obj (op W)),
      (cofanFinsetDesc c S).hom.app (op W) y = s := by
  classical
  obtain ⟨R, hR, hsum⟩ := exists_mem_forall_eq_sum_of_isColimit_cofan hc s
  obtain ⟨n, U, g, hRg, -, hcov⟩ := (AlgebraicGeometry.Etale.exists_affine_refinement _) hR
  choose S x hx using fun a ↦ hsum (g a) (hRg a)
  let S₀ : Finset ι := Finset.univ.biUnion S
  have hS (a : Fin n) : S a ⊆ S₀ := Finset.subset_biUnion_of_mem S (Finset.mem_univ a)
  -- the local lifts to `⨁_{i ∈ S₀} Fᵢ`
  let z (a : Fin n) : (⨁ fun i : S₀ ↦ F i.1).obj.obj (op (U a)) :=
    (biproduct.desc (fun i : S a ↦ biproduct.ι (fun i : S₀ ↦ F i.1) ⟨i.1, hS a i.2⟩)).hom.app _
      (∑ i : S a, (biproduct.ι (fun i : S a ↦ F i.1) i).hom.app _ (x a i))
  have hz (a : Fin n) : (cofanFinsetDesc c S₀).hom.app _ (z a) = c.pt.obj.map (g a).op s := by
    rw [hx a, sum_eq_cofanFinsetDesc_app, cofanFinsetDesc_eq_comp (hS a)]
    rfl
  obtain ⟨y, hy, -⟩ := ((Presieve.isSheafFor_arrows_iff_pullbacks _ g).1
    (isSheafFor_ofArrows _ g hcov)) z fun a b ↦ injective_cofanFinsetDesc_app hc S₀ _ (by
      change (cofanFinsetDesc c S₀).hom.app _ ((⨁ fun i : S₀ ↦ F i.1).obj.map _ (z a)) =
        (cofanFinsetDesc c S₀).hom.app _ ((⨁ fun i : S₀ ↦ F i.1).obj.map _ (z b))
      rw [NatTrans.naturality_apply, NatTrans.naturality_apply, hz, hz,
        ← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← Functor.map_comp,
        ← Functor.map_comp, ← op_comp, ← op_comp, pullback.condition])
  refine ⟨S₀, y, (isSheafFor_ofArrows c.pt g hcov).isSeparatedFor.ext ?_⟩
  rintro Z f ⟨a⟩
  change c.pt.obj.map _ _ = c.pt.obj.map _ _
  rw [← NatTrans.naturality_apply]
  erw [hy a]
  exact hz a
end FiniteSum


section QCQS

/-- Quasi-compactness and quasi-separatedness of the underlying scheme are invariant under
isomorphisms of étale `X`-schemes. -/
lemma compactSpace_and_quasiSeparatedSpace_of_iso {A B : X.Etale} (e : A ≅ B)
    (h : CompactSpace A.left ∧ QuasiSeparatedSpace A.left) :
    CompactSpace B.left ∧ QuasiSeparatedSpace B.left := by
  let φ := TopCat.homeoOfIso (Scheme.forgetToTop.mapIso ((Etale.forget X ⋙ Over.forget X).mapIso e))
  exact ⟨@Homeomorph.compactSpace _ _ _ _ h.1 φ, (quasiSeparatedSpace_congr φ).1 h.2⟩

/-- A fibre product of étale `X`-schemes with quasi-compact quasi-separated underlying schemes
over one with quasi-separated underlying scheme has quasi-compact quasi-separated underlying
scheme. -/
lemma compactSpace_and_quasiSeparatedSpace_pullback {V A B : X.Etale} (f : A ⟶ V) (g : B ⟶ V)
    [QuasiSeparatedSpace V.left] [CompactSpace A.left] [QuasiSeparatedSpace A.left]
    [CompactSpace B.left] [QuasiSeparatedSpace B.left] :
    CompactSpace (pullback f g).left ∧ QuasiSeparatedSpace (pullback f g).left := by
  let iso := PreservesPullback.iso (Etale.forget X ⋙ Over.forget X) f g
  have : QuasiCompact f.left := quasiCompact_of_compactSpace _
  have : CompactSpace ↥(Limits.pullback (C := Scheme.{u}) f.left g.left) := inferInstance
  have : QuasiSeparatedSpace ↥(Limits.pullback (C := Scheme.{u}) f.left g.left) :=
    quasiSeparatedSpace_of_quasiSeparated (pullback.snd f.left g.left)
  let φ := TopCat.homeoOfIso (Scheme.forgetToTop.mapIso iso).symm
  exact ⟨@Homeomorph.compactSpace _ _ _ _ ‹_› φ, (quasiSeparatedSpace_congr φ).1 ‹_›⟩

/-- A finite product in `Over V` of étale `X`-schemes with quasi-compact quasi-separated
underlying schemes has quasi-compact quasi-separated underlying scheme, if `V` has. -/
lemma compactSpace_and_quasiSeparatedSpace_piObj {V : X.Etale} [CompactSpace V.left]
    [QuasiSeparatedSpace V.left] {J : Type*} [Finite J] (U : J → Over V)
    (hU : ∀ j, CompactSpace (U j).left.left ∧ QuasiSeparatedSpace (U j).left.left) :
    CompactSpace (∏ᶜ U).left.left ∧ QuasiSeparatedSpace (∏ᶜ U).left.left := by
  let P : ObjectProperty (Over V) := fun A ↦
    CompactSpace A.left.left ∧ QuasiSeparatedSpace A.left.left
  have hiso {A B : Over V} (e : A ≅ B) (h : P A) : P B :=
    compactSpace_and_quasiSeparatedSpace_of_iso ((Over.forget V).mapIso e) h
  have : P.IsClosedUnderLimitsOfShape (Discrete.{0} PEmpty) := ⟨by
    rintro A ⟨h⟩
    have hA : IsTerminal A := (isLimitEquivIsTerminalOfIsEmpty _ _) h.isLimit
    exact hiso (Over.mkIdTerminal.uniqueUpToIso hA) ⟨‹_›, ‹_›⟩⟩
  have : P.IsClosedUnderBinaryProducts := ⟨by
    rintro A ⟨h⟩
    let e : A ≅ h.diag.obj ⟨.left⟩ ⨯ h.diag.obj ⟨.right⟩ :=
      h.isLimit.conePointUniqueUpToIso (limit.isLimit _) ≪≫ HasLimit.isoOfNatIso (diagramIsoPair _)
    refine hiso e.symm ?_
    obtain ⟨_, _⟩ := h.prop_diag_obj ⟨.left⟩
    obtain ⟨_, _⟩ := h.prop_diag_obj ⟨.right⟩
    exact compactSpace_and_quasiSeparatedSpace_of_iso (Over.prodLeftIsoPullback _ _).symm
      (compactSpace_and_quasiSeparatedSpace_pullback _ _)⟩
  have : P.IsClosedUnderFiniteProducts := .mk'
  exact P.prop_product hU

end QCQS

section Cech



open Presheaf

variable {ι : Type u} {F : ι → Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}} {c : Cofan F}

/-- Let `c` be a coproduct of injective abelian étale sheaves `Fᵢ` on `X`. On a finite family of
étale `X`-schemes over `V` whose Čech nerve has quasi-compact members, the Čech complex of `c.pt`
is exact in positive degrees. Indeed every Čech cochain comes from the finite sum
`⨁_{i ∈ S} Fᵢ` for some finite `S`, which is injective. -/
lemma exactAt_cechComplex_of_isColimit_cofan [∀ i, Injective (F i)] (hc : IsColimit c)
    {V : X.Etale} {n : ℕ} (U : Fin n → Over V)
    (hU : ∀ (k : ℕ) (y : Fin (k + 1) → Fin n), CompactSpace (cechNerveObj U y).left.left)
    (q : ℕ) : ((cechComplex U).obj c.pt.obj).ExactAt (q + 1) := by
  classical
  rw [exactAt_cechComplex_iff]
  intro z hz
  choose S w hw using fun y : Fin (q + 2) → Fin n ↦
    @exists_cofanFinsetDesc_app_eq _ _ _ _ hc _ (hU (q + 1) y) (z y)
  let S₀ : Finset ι := Finset.univ.biUnion S
  have hS (y : Fin (q + 2) → Fin n) : S y ⊆ S₀ :=
    Finset.subset_biUnion_of_mem S (Finset.mem_univ y)
  let z' : ((cechComplex U).obj (⨁ fun i : S₀ ↦ F i.1).obj).X (q + 1) := fun y ↦
    (biproduct.desc (fun i : S y ↦ biproduct.ι (fun i : S₀ ↦ F i.1) ⟨i.1, hS y i.2⟩)).hom.app _
      (w y)
  have hz' : ((cechComplex U).map (cofanFinsetDesc c S₀).hom).f (q + 1) z' = z := by
    funext y
    rw [cechComplex_map_f_apply, ← hw y, cofanFinsetDesc_eq_comp (hS y)]
    rfl
  have hinj := cechComplex_map_f_injective U _ (injective_cofanFinsetDesc_app hc S₀)
  obtain ⟨b, hb⟩ := (exactAt_cechComplex_iff U _ q).1
    (Sheaf.exactAt_cechComplex_of_injective (⨁ fun i : S₀ ↦ F i.1) U q) z'
    (hinj _ (by rw [cechComplex_map_f_d_apply, hz', hz, map_zero]))
  exact ⟨((cechComplex U).map (cofanFinsetDesc c S₀).hom).f q b, by
    rw [← cechComplex_map_f_d_apply, hb, hz']⟩

variable (X) in
/-- On a quasi-compact quasi-separated scheme `X`, a direct sum of injective abelian étale
sheaves has no higher cohomology. This follows from the Čech criterion
`CategoryTheory.Sheaf.subsingleton_H_succ_of_exactAt_cechComplex` applied to the étale
`X`-schemes with quasi-compact quasi-separated underlying scheme, by
`AlgebraicGeometry.Scheme.exactAt_cechComplex_of_isColimit_cofan`. -/
theorem subsingleton_H_succ_of_isColimit_cofan_of_injective [CompactSpace X]
    [QuasiSeparatedSpace X] [∀ i, Injective (F i)] (hc : IsColimit c) (q : ℕ) :
    Subsingleton (Sheaf.H c.pt (q + 1)) := by
  let T : X.Etale := Etale.mk (𝟙 X)
  have hT : IsTerminal T := MorphismProperty.Over.mkIdTerminal _ X
  let B : X.Etale → Prop := fun W ↦ CompactSpace W.left ∧ QuasiSeparatedSpace W.left
  have hcov (V : X.Etale) (hV : B V) (R : Sieve V) (hR : R ∈ X.smallEtaleTopology V) :
      ∃ (n : ℕ) (U : Fin n → Over V),
        (∀ (k : ℕ) (y : Fin (k + 1) → Fin n), B (cechNerveObj U y).left) ∧ (∀ a, R (U a).hom) ∧
        Sieve.ofArrows (fun a ↦ (U a).left) (fun a ↦ (U a).hom) ∈ X.smallEtaleTopology V := by
    obtain ⟨_, _⟩ := hV
    obtain ⟨n, U, g, hRg, hU, hg⟩ := (AlgebraicGeometry.Etale.exists_affine_refinement _) hR
    refine ⟨n, fun a ↦ Over.mk (g a), fun k y ↦ ?_, hRg,
      (ofArrows_mem_smallEtaleTopology_iff g).2 hg⟩
    refine compactSpace_and_quasiSeparatedSpace_piObj _ fun l ↦ ?_
    have := hU (y l)
    exact ⟨inferInstanceAs (CompactSpace (U (y l)).left),
      inferInstanceAs (QuasiSeparatedSpace (U (y l)).left)⟩
  exact Sheaf.subsingleton_H_succ_of_exactAt_cechComplex hT B
    ⟨‹CompactSpace X›, ‹QuasiSeparatedSpace X›⟩ hcov c.pt
    (fun V hV n U hU _ q ↦ exactAt_cechComplex_of_isColimit_cofan hc U (fun k y ↦ (hU k y).1) q) q

end Cech

open Abelian in
/-- **Étale cohomology commutes with direct sums on a qcqs scheme.** Let `X` be quasi-compact
and quasi-separated and let `c` be a coproduct of a family `F` of abelian étale sheaves on `X`.
If `Hⁿ(X, Fᵢ) = 0` for all `i`, then `Hⁿ(X, c.pt) = 0`. -/
@[stacks 03Q6]
theorem subsingleton_H_of_isColimit_cofan (X : Scheme.{u}) [CompactSpace X]
    [QuasiSeparatedSpace X] {ι : Type u} {F : ι → Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}}
    {c : Cofan F} (hc : IsColimit c) (n : ℕ) (hF : ∀ i, Subsingleton (Sheaf.H (F i) n)) :
    Subsingleton (Sheaf.H c.pt n) := by
  let T : X.Etale := Etale.mk (𝟙 X)
  have hT : IsTerminal T := MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale _
  rcases n with _ | n
  · -- in degree zero, a global section is a finite sum of global sections of the `Fᵢ`
    have : CompactSpace T.left := ‹CompactSpace X›
    refine ⟨fun a b ↦ (Sheaf.H.equiv₀ c.pt hT).injective ?_⟩
    have key (s : c.pt.obj.obj (op T)) : s = 0 := by
      obtain ⟨S, y, rfl⟩ := exists_cofanFinsetDesc_app_eq hc s
      have (i : S) : Subsingleton (Sheaf.H (F i.1) 0) := hF i.1
      have : Subsingleton (Sheaf.H (⨁ fun i : S ↦ F i.1) 0) :=
        (Abelian.Ext.addEquivBiproduct _ (biproduct.isBilimit _) 0).toEquiv.subsingleton
      rw [← (Sheaf.H.equiv₀ _ hT).apply_symm_apply y, Subsingleton.elim
        ((Sheaf.H.equiv₀ _ hT).symm y) 0, map_zero, map_zero]
    rw [key (Sheaf.H.equiv₀ c.pt hT a), key (Sheaf.H.equiv₀ c.pt hT b)]
  induction n generalizing ι F c with
  | zero => exact subsingleton_H_one_of_isColimit_cofan X hc hF
  | succ n ih =>
    -- dimension shifting along `0 → ⨁ Fᵢ → ⨁ Iᵢ → ⨁ Qᵢ → 0` with `Iᵢ` injective
    have : HasCoproducts.{u} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) := fun _ ↦
      ⟨fun _ ↦ HasColimit.mk ⟨Sheaf.sheafifyCocone (colimit.cocone _),
        Sheaf.isColimitSheafifyCocone _ (colimit.isColimit _)⟩⟩
    have : HasCoproducts.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) := fun _ ↦
      ⟨fun _ ↦ HasColimit.mk ⟨Sheaf.sheafifyCocone (colimit.cocone _),
        Sheaf.isColimitSheafifyCocone _ (colimit.isColimit _)⟩⟩
    have : HasExactColimitsOfShape (Discrete (ULift.{u + 1} ι))
        (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) := AB4OfSize.ofShape _
    have : HasExactColimitsOfShape (Discrete ι)
        (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
      HasExactColimitsOfShape.of_domain_equivalence _
        (Discrete.equivalence Equiv.ulift.{u + 1})
    let I (i : ι) := Injective.under (F i)
    let Q (i : ι) := cokernel (Injective.ι (F i))
    let f : c.pt ⟶ ∐ I := Cofan.IsColimit.desc hc fun i ↦ Injective.ι (F i) ≫ Sigma.ι I i
    let g : ∐ I ⟶ ∐ Q := Limits.Sigma.map fun i ↦ cokernel.π (Injective.ι (F i))
    have hf (i : ι) : c.inj i ≫ f = Injective.ι (F i) ≫ Sigma.ι I i := Cofan.IsColimit.fac _ _ _
    have hfg : f ≫ g = 0 := Cofan.IsColimit.hom_ext hc _ _ fun i ↦ by
      rw [reassoc_of% (hf i)]
      simp [g]
    let S := ShortComplex.mk f g hfg
    let φ : Discrete.functor F ⟶ Discrete.functor I :=
      Discrete.natTrans fun i ↦ Injective.ι (F i.as)
    have : ∀ j, Mono (φ.app j) := fun ⟨i⟩ ↦ (inferInstance : Mono (Injective.ι (F i)))
    have : Mono φ := NatTrans.mono_of_mono_app φ
    have : Mono f := colim.map_mono' φ hc (colimit.isColimit _) f fun ⟨i⟩ ↦ hf i
    have : ∀ j : Discrete ι, Epi ((Discrete.natTrans (F := Discrete.functor I)
        (G := Discrete.functor Q) fun i ↦ cokernel.π (Injective.ι (F i.as))).app j) :=
      fun ⟨i⟩ ↦ (inferInstance : Epi (cokernel.π (Injective.ι (F i))))
    have : Epi g := colim.map_epi' (J := Discrete ι)
      (Discrete.natTrans fun i ↦ cokernel.π (Injective.ι (F i.as))) (colimit.cocone _)
      (colimit.isColimit _) g fun ⟨i⟩ ↦ by simp [g]
    have hg : IsColimit (CokernelCofork.ofπ (f := f) g hfg) := by
      refine CokernelCofork.IsColimit.ofπ _ _
        (fun {Z} h hh ↦ Sigma.desc fun i ↦ cokernel.desc _ (Sigma.ι I i ≫ h) (by
          rw [← reassoc_of% (hf i), hh, comp_zero]))
        (fun {Z} h hh ↦ Sigma.hom_ext _ _ fun i ↦ by simp [g])
        (fun {Z} h hh m hm ↦ Sigma.hom_ext _ _ fun i ↦ by
          rw [← cancel_epi (cokernel.π (Injective.ι (F i)))]
          simp [← hm, g])
    have hS : S.ShortExact := .mk' (S.exact_of_g_is_cokernel hg) inferInstance inferInstance
    -- `H^{n + 1}(Qᵢ) = 0` and `H^{n + 2}(⨁ Iᵢ) = 0`
    have hQ (i : ι) : Subsingleton (Sheaf.H (Q i) (n + 1)) := by
      let Sᵢ := ShortComplex.mk (Injective.ι (F i)) (cokernel.π (Injective.ι (F i)))
        (cokernel.condition _)
      have hSᵢ : Sᵢ.ShortExact :=
        .mk' (ShortComplex.exact_cokernel _) inferInstance inferInstance
      refine subsingleton_of_forall_eq 0 fun y ↦ ?_
      have := hF i
      obtain ⟨x, rfl⟩ := Ext.covariant_sequence_exact₃ _ hSᵢ y rfl (Subsingleton.elim _ _)
      rw [Ext.eq_zero_of_injective x, Ext.zero_comp]
    have h₃ := ih (colimit.isColimit (Discrete.functor Q)) hQ
    have h₂ := subsingleton_H_succ_of_isColimit_cofan_of_injective X
      (colimit.isColimit (Discrete.functor I)) (n + 1)
    refine subsingleton_of_forall_eq 0 fun x ↦ ?_
    obtain ⟨y, rfl⟩ := Ext.covariant_sequence_exact₁ _ hS x (Subsingleton.elim (h := h₂) _ _) rfl
    rw [Subsingleton.elim (h := h₃) y 0, Ext.zero_comp]

end AlgebraicGeometry.Scheme
