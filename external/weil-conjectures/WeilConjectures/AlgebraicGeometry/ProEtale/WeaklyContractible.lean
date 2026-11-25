/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Sites.WeaklyContractible
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.AlgebraicGeometry.ProEtale.Flat.QuasiCompactCover
public import WeilConjectures.AlgebraicGeometry.Morphisms.WeaklyEtale
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
public import WeilConjectures.RingTheory.ProEtale.WeaklyEtaleIndEtale
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-!
# Weakly contractible objects of the small pro-étale site

We show that the small pro-étale site of a scheme `T` has enough affine weakly contractible
objects (Stacks 0990), and deduce that vanishing of sheaves and acyclicity of complexes of
sheaves of modules can be detected on sections over affine weakly contractible objects.

## Main results

- `AlgebraicGeometry.Scheme.ProEt.isWeaklyContractible_of_iso`: an object whose underlying
  scheme is the spectrum of a w-contractible ring is weakly contractible.
- `AlgebraicGeometry.Scheme.ProEt.exists_isWeaklyContractible_cover`: every object is covered
  by affine weakly contractible objects.
- `AlgebraicGeometry.ProEtale.isZero_iff_forall_isWeaklyContractible`: a sheaf of modules
  vanishes iff its sections over affine weakly contractible objects vanish.
- `AlgebraicGeometry.ProEtale.acyclic_iff_forall_isWeaklyContractible`: a complex of sheaves
  of modules is acyclic iff its sections over affine weakly contractible objects are acyclic.
-/

@[expose] public section

universe w u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

/-- A surjective weakly étale morphism from an affine scheme to `Spec R` has a section, if every
faithfully flat ind-étale `R`-algebra has a retraction. -/
lemma exists_comp_eq_id_of_forall_exists_retraction {R : CommRingCat.{u}}
    (hR : ∀ (T : Type u) [CommRing T] [Algebra R T] [Algebra.IndEtale R T]
      [Module.FaithfullyFlat R T], ∃ f : T →+* R, f.comp (algebraMap R T) = RingHom.id R)
    {Y : Scheme.{u}} [IsAffine Y] (p : Y ⟶ Spec R) [WeaklyEtale p] [Surjective p] :
    ∃ s : Spec R ⟶ Y, s ≫ p = 𝟙 _ := by
  obtain ⟨φ, hφ⟩ : ∃ φ : R ⟶ Γ(Y, ⊤), Spec.map φ = Y.isoSpec.inv ≫ p :=
    ⟨Spec.preimage _, Spec.map_preimage _⟩
  have : WeaklyEtale (Spec.map φ) := by
    rw [hφ]
    infer_instance
  have : Surjective (Spec.map φ) := by
    rw [hφ]
    infer_instance
  have hff : φ.hom.FaithfullyFlat := (flat_and_surjective_SpecMap_iff φ).1 ⟨inferInstance, ‹_›⟩
  obtain ⟨T, _, g, hg, hgff, hgφ⟩ := ((WeaklyEtale.Spec_iff φ).1 ‹_›).exists_indEtale_comp
  algebraize [g.comp φ.hom]
  have : Algebra.IndEtale R T := by
    rwa [← RingHom.IndEtale.algebraMap_iff]
  have : Module.FaithfullyFlat R T := by
    rw [← RingHom.faithfullyFlat_algebraMap_iff]
    exact RingHom.FaithfullyFlat.stableUnderComposition _ _ hff hgff
  obtain ⟨r, hr⟩ := hR T
  refine ⟨Spec.map (CommRingCat.ofHom (r.comp g)) ≫ Y.isoSpec.inv, ?_⟩
  rw [Category.assoc, ← hφ, ← Spec.map_comp, ← Spec.map_id]
  congr 1
  ext x
  exact RingHom.congr_fun hr x

/-- A surjective weakly étale morphism from an affine scheme to the spectrum of a
w-contractible ring has a section. -/
lemma exists_comp_eq_id_of_isWContractibleRing {R : CommRingCat.{u}} [IsWContractibleRing R]
    {Y : Scheme.{u}} [IsAffine Y] (p : Y ⟶ Spec R) [WeaklyEtale p] [Surjective p] :
    ∃ s : Spec R ⟶ Y, s ≫ p = 𝟙 _ :=
  exists_comp_eq_id_of_forall_exists_retraction
    (fun T _ _ _ _ ↦ IsWContractibleRing.exists_retraction R T) p

/-- Let `s` be a section of a morphism `∐ V j ⟶ X`. The preimages under `s` of the components
`V j` form a cover of `X` by pairwise disjoint open subschemes, and the inclusion of the `j`-th
one factors through `V j ⟶ X`. -/
lemma exists_disjoint_opens_of_comp_sigmaDesc_eq_id {X : Scheme.{u}} {κ : Type u}
    {V : κ → Scheme.{u}} (v : ∀ j, V j ⟶ X) (s : X ⟶ ∐ V) (hs : s ≫ Sigma.desc v = 𝟙 _) :
    ∃ O : κ → X.Opens, (∀ i j, i ≠ j → Disjoint (O i) (O j)) ∧ (∀ x, ∃ i, x ∈ O i) ∧
      ∀ j, ∃ c : (O j).toScheme ⟶ V j, c ≫ v j = (O j).ι := by
  let O (j : κ) : X.Opens := s ⁻¹ᵁ (Sigma.ι V j).opensRange
  have hO (j : κ) : Set.range ((O j).ι ≫ s).base ⊆ Set.range (Sigma.ι V j).base := by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Scheme.Opens.range_ι]
    rintro _ ⟨x, hx, rfl⟩
    exact hx
  refine ⟨O, fun i j hij ↦ ?_, fun x ↦ ?_, fun j ↦
    ⟨IsOpenImmersion.lift (Sigma.ι V j) ((O j).ι ≫ s) (hO j), ?_⟩⟩
  · rw [disjoint_iff, eq_bot_iff]
    rintro x ⟨hi, hj⟩
    exact (disjoint_opensRange_sigmaι V i j hij).le_bot ⟨hi, hj⟩
  · obtain ⟨j, y, hy⟩ := (sigmaOpenCover V).exists_eq (s x)
    exact ⟨j, ⟨y, hy⟩⟩
  · rw [← Sigma.ι_comp_desc v j, ← Category.assoc, IsOpenImmersion.lift_fac, Category.assoc, hs,
      Category.comp_id]

namespace Scheme.ProEt

variable {T : Scheme.{u}}

/-- Let `W` be an object of the small pro-étale site whose underlying scheme admits a section
`s` of a morphism `∐ V j ⟶ W.left`. The preimages under `s` of the components `V j` form a
covering family of `W` by pairwise disjoint open immersions, and each of them factors through
`V j`; in particular they lie in every sieve `S` containing all the morphisms to `W` factoring
through some `V j`. -/
lemma exists_disjoint_cover_of_comp_sigmaDesc_eq_id {W : T.ProEt} {κ : Type u}
    {V : κ → Scheme.{u}} (v : ∀ j, V j ⟶ W.left) (s : W.left ⟶ ∐ V)
    (hs : s ≫ Sigma.desc v = 𝟙 _) (S : Sieve W)
    (hS : ∀ j {Y : T.ProEt} (a : Y ⟶ W) (b : Y.left ⟶ V j), b ≫ v j = a.left → S a) :
    ∃ (ι : Type u) (Y : ι → T.ProEt) (f : ∀ i, Y i ⟶ W),
      Sieve.ofArrows Y f ∈ topology T W ∧ (∀ i, S (f i)) ∧ (∀ i, Mono (f i)) ∧
      ∀ i j, i ≠ j → ∀ (Z : T.ProEt) (a : Z ⟶ Y i) (b : Z ⟶ Y j), a ≫ f i = b ≫ f j →
        ⊥ ∈ topology T Z := by
  obtain ⟨O, hdisj, hcov, hc⟩ := exists_disjoint_opens_of_comp_sigmaDesc_eq_id v s hs
  refine ⟨κ, fun j ↦ ofOpenImmersion W (O j).ι, fun j ↦ ofOpenImmersionHom W (O j).ι,
    ?_, fun j ↦ hS j _ (hc j).choose (hc j).choose_spec, fun j ↦ ?_, ?_⟩
  · refine mem_topology_of_openImmersion _ (fun j ↦ (O j).ι) (fun x ↦ ?_)
      (fun j ↦ Sieve.ofArrows_mk _ _ j)
    obtain ⟨j, hj⟩ := hcov x
    exact ⟨j, by rw [Opens.range_ι]; exact hj⟩
  · refine (ProEt.forget T ⋙ CategoryTheory.Over.forget T).mono_of_mono_map ?_
    exact inferInstanceAs (Mono (O j).ι)
  · intro i j hij Z a b hab
    have : IsEmpty Z.left := by
      refine ⟨fun z ↦ ?_⟩
      have hab' : a.left ≫ (O i).ι = b.left ≫ (O j).ι := congrArg (fun g ↦ g.left) hab
      have hi : (a.left ≫ (O i).ι).base z ∈ O i :=
        (Opens.range_ι (O i)).subset ⟨a.left z, rfl⟩
      have hj : (a.left ≫ (O i).ι).base z ∈ O j := by
        rw [hab']
        exact (Opens.range_ι (O j)).subset ⟨b.left z, rfl⟩
      exact (disjoint_iff.1 (hdisj i j hij)).le ⟨hi, hj⟩
    exact bot_mem_topology Z

/-- Let `W ≅ Spec R` be an object of the small pro-étale site, where every faithfully flat
ind-étale `R`-algebra has a retraction, and `S` a covering sieve of `W`. Then there is a morphism
`∐ V j ⟶ W.left` with a section, such that every morphism to `W` factoring through some `V j`
lies in `S`. -/
lemma exists_comp_sigmaDesc_eq_id_of_forall_exists_retraction {W : T.ProEt}
    {R : CommRingCat.{u}}
    (hR : ∀ (T : Type u) [CommRing T] [Algebra R T] [Algebra.IndEtale R T]
      [Module.FaithfullyFlat R T], ∃ f : T →+* R, f.comp (algebraMap R T) = RingHom.id R)
    (e : W.left ≅ Spec R) {S : Sieve W} (hS : S ∈ topology T W) :
    ∃ (κ : Type u) (V : κ → Scheme.{u}) (v : ∀ j, V j ⟶ W.left) (s : W.left ⟶ ∐ V),
      s ≫ Sigma.desc v = 𝟙 _ ∧
      ∀ j {Y : T.ProEt} (a : Y ⟶ W) (b : Y.left ⟶ V j), b ≫ v j = a.left → S a := by
  obtain ⟨P, hP, hPS⟩ := mem_topology_iff.1 hS
  obtain ⟨𝒰, _, h𝒰⟩ := (mem_propQCPrecoverage_iff_exists_quasiCompactCover
    (P := @WeaklyEtale)).1 (mem_precoverage_iff.1 hP)
  have : IsAffine W.left := .of_isIso e.hom
  obtain ⟨𝒱, g, _, _⟩ := Cover.QuasiCompact.exists_hom.{u + 1, u} 𝒰
  have hmem (i : 𝒰.I₀) : P.map (ProEt.forget T ⋙ CategoryTheory.Over.forget T) (𝒰.f i) := by
    rw [h𝒰]
    exact ⟨i⟩
  choose Z hZ a ha hZa using fun i ↦ Presieve.map_iff.1 (hmem i)
  -- Reindex the finite affine refinement by a type in `Type u`.
  let ε : ULift.{u} (Fin (Nat.card 𝒱.I₀)) ≃ 𝒱.I₀ := Equiv.ulift.trans (Finite.equivFin _).symm
  let v (k : ULift.{u} (Fin (Nat.card 𝒱.I₀))) := 𝒱.f (ε k)
  have : WeaklyEtale (Sigma.desc v) := IsZariskiLocalAtSource.sigmaDesc fun k ↦ 𝒱.map_prop _
  have : Surjective (Sigma.desc v) := by
    refine Surjective.sigmaDesc_of_union_range_eq_univ (Set.eq_univ_of_forall fun x ↦ ?_)
    obtain ⟨k, hk⟩ := ε.surjective (𝒱.idx x)
    refine Set.mem_iUnion.2 ⟨k, ?_⟩
    simp only [v]
    rw [hk]
    exact 𝒱.covers x
  obtain ⟨s, hs⟩ := exists_comp_eq_id_of_forall_exists_retraction hR (Sigma.desc v ≫ e.hom)
  refine ⟨_, _, v, e.hom ≫ s, ?_, ?_⟩
  · rw [← cancel_mono e.hom, Category.assoc, Category.assoc, hs]
    simp
  · intro j Y b c hbc
    have ha' (i : 𝒰.I₀) : (a i).left = eqToHom (hZ i) ≫ 𝒰.f i := hZa i
    let d : Y.left ⟶ (Z (g.s₀ (ε j))).left := c ≫ g.h₀ (ε j) ≫ eqToHom (hZ _).symm
    have hd : d ≫ (a (g.s₀ (ε j))).left = b.left := by
      rw [← hbc, ha', Category.assoc, Category.assoc, eqToHom_trans_assoc, eqToHom_refl,
        Category.id_comp, g.w₀]
      rfl
    have hb : b = MorphismProperty.Over.homMk d (by
        rw [← MorphismProperty.Over.w (a (g.s₀ (ε j))), ← Category.assoc, hd]
        exact MorphismProperty.Over.w b) ≫ a (g.s₀ (ε j)) :=
      MorphismProperty.Over.Hom.ext hd.symm
    rw [hb]
    exact S.downward_closed (hPS _ _ (ha _)) _

/-- Let `W ≅ Spec R` be an object of the small pro-étale site, where every faithfully flat
ind-étale `R`-algebra has a retraction. Every covering sieve of `W` contains the inclusions of a
cover of `W` by pairwise disjoint open subschemes. -/
lemma exists_disjoint_opens_of_forall_exists_retraction {W : T.ProEt} {R : CommRingCat.{u}}
    (hR : ∀ (T : Type u) [CommRing T] [Algebra R T] [Algebra.IndEtale R T]
      [Module.FaithfullyFlat R T], ∃ f : T →+* R, f.comp (algebraMap R T) = RingHom.id R)
    (e : W.left ≅ Spec R) {S : Sieve W} (hS : S ∈ topology T W) :
    ∃ (κ : Type u) (O : κ → W.left.Opens), (∀ i j, i ≠ j → Disjoint (O i) (O j)) ∧
      (∀ x, ∃ i, x ∈ O i) ∧ ∀ i, S (ofOpenImmersionHom W (O i).ι) := by
  obtain ⟨κ, V, v, s, hs, hSv⟩ := exists_comp_sigmaDesc_eq_id_of_forall_exists_retraction hR e hS
  obtain ⟨O, hdisj, hcov, hc⟩ := exists_disjoint_opens_of_comp_sigmaDesc_eq_id v s hs
  exact ⟨κ, O, hdisj, hcov, fun j ↦ hSv j _ (hc j).choose (hc j).choose_spec⟩

/-- **Stacks 0990**, variant: an object of the small pro-étale site whose underlying scheme is
`Spec R`, where every faithfully flat ind-étale `R`-algebra has a retraction, is weakly
contractible. -/
@[stacks 0990]
theorem isWeaklyContractible_of_forall_exists_retraction {W : T.ProEt} {R : CommRingCat.{u}}
    (hR : ∀ (T : Type u) [CommRing T] [Algebra R T] [Algebra.IndEtale R T]
      [Module.FaithfullyFlat R T], ∃ f : T →+* R, f.comp (algebraMap R T) = RingHom.id R)
    (e : W.left ≅ Spec R) : (topology T).IsWeaklyContractible.{w} W := by
  refine GrothendieckTopology.isWeaklyContractible_of_forall_mem.{w, u} fun S hS ↦ ?_
  obtain ⟨κ, V, v, s, hs, hSv⟩ := exists_comp_sigmaDesc_eq_id_of_forall_exists_retraction hR e hS
  exact exists_disjoint_cover_of_comp_sigmaDesc_eq_id v s hs S hSv

/-- **Stacks 0990.** An object of the small pro-étale site whose underlying scheme is the
spectrum of a w-contractible ring is weakly contractible
(see `isWeaklyContractible_of_forall_exists_retraction`). -/
@[stacks 0990]
theorem isWeaklyContractible_of_iso {W : T.ProEt} {R : CommRingCat.{u}} [IsWContractibleRing R]
    (e : W.left ≅ Spec R) : (topology T).IsWeaklyContractible.{w} W :=
  isWeaklyContractible_of_forall_exists_retraction
    (fun T _ _ _ _ ↦ IsWContractibleRing.exists_retraction R T) e

/-- **Stacks 0990.** The small pro-étale site has enough affine weakly contractible objects:
every object `V` is covered by objects `W i` whose underlying schemes are spectra of
w-contractible rings. Cover `V` by affine opens `Spec R` (a Zariski covering), and each
`Spec R` by `Spec S`, for a faithfully flat, ind-étale and w-contractible `R`-algebra `S`. -/
@[stacks 0990]
theorem exists_isWeaklyContractible_cover (V : T.ProEt) :
    ∃ (ι : Type u) (W : ι → T.ProEt) (f : ∀ i, W i ⟶ V),
      (∀ i, IsAffine (W i).left ∧ (topology T).IsWeaklyContractible.{w} (W i)) ∧
      Sieve.ofArrows W f ∈ topology T V := by
  have 𝒜 : V.left.AffineOpenCover := V.left.affineOpenCover
  choose S iS iA hind hff hw using fun x : 𝒜.I₀ ↦ exists_isWContractibleRing (𝒜.X x)
  let φ (x : 𝒜.I₀) : 𝒜.X x ⟶ CommRingCat.of (S x) := CommRingCat.ofHom (algebraMap _ _)
  have (x : 𝒜.I₀) : WeaklyEtale (Spec.map (φ x)) := by
    rw [WeaklyEtale.Spec_iff]
    exact RingHom.IndEtale.weaklyEtale ((RingHom.IndEtale.algebraMap_iff _ _).2 (hind x))
  have (x : 𝒜.I₀) : Surjective (Spec.map (φ x)) :=
    ((flat_and_surjective_SpecMap_iff (φ x)).2
      (RingHom.faithfullyFlat_algebraMap_iff.2 (hff x))).2
  let U (x : 𝒜.I₀) := ofOpenImmersion V (𝒜.f x)
  let W (x : 𝒜.I₀) : T.ProEt := ProEt.mk (Spec.map (φ x) ≫ (U x).hom)
  let w (x : 𝒜.I₀) : W x ⟶ U x := MorphismProperty.Over.homMk (Spec.map (φ x)) rfl
  refine ⟨𝒜.I₀, W, fun x ↦ w x ≫ ofOpenImmersionHom V (𝒜.f x), fun x ↦ ⟨?_, ?_⟩, ?_⟩
  · exact inferInstanceAs (IsAffine (Spec _))
  · have := hw x
    exact isWeaklyContractible_of_iso (R := CommRingCat.of (S x)) (Iso.refl _)
  · have hU : Sieve.ofArrows U (fun x ↦ ofOpenImmersionHom V (𝒜.f x)) ∈ topology T V :=
      mem_topology_of_openImmersion _ 𝒜.f (fun y ↦ ⟨_, 𝒜.covers y⟩)
        (fun x ↦ Sieve.ofArrows_mk _ _ x)
    refine (topology T).transitive hU _ fun Y g hg ↦ ?_
    obtain ⟨_, c, _, ⟨x⟩, rfl⟩ := hg
    rw [Sieve.pullback_comp]
    refine (topology T).pullback_stable c ((topology T).superset_covering ?_
      (Precoverage.generate_mem_toGrothendieck (R := .singleton (w x)) ?_))
    · rintro _ _ ⟨_, d, _, ⟨⟩, rfl⟩
      rw [Sieve.pullback_apply, Category.assoc]
      exact (Sieve.ofArrows _ _).downward_closed (Sieve.ofArrows_mk _ _ x) d
    · rw [mem_precoverage_iff, Presieve.map_singleton]
      exact Hom.singleton_mem_propQCPrecoverage (P := @WeaklyEtale) (f := Spec.map (φ x))
        inferInstance

end Scheme.ProEt
namespace ProEtale

variable {T : Scheme.{u}} {Λ : Type (u + 1)} [CommRing Λ]

/-- **Detection of vanishing** (Stacks 0990, 090M): a sheaf of `Λ`-modules on the small
pro-étale site vanishes if and only if its sections over all affine weakly contractible objects
vanish. -/
@[stacks 0990]
theorem isZero_iff_forall_isWeaklyContractible
    (F : Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} Λ)) :
    IsZero F ↔ ∀ W : T.ProEt, IsAffine W.left →
      (Scheme.ProEt.topology T).IsWeaklyContractible.{u + 1} W →
        Subsingleton (F.obj.obj (op W)) := by
  rw [GrothendieckTopology.isZero_sheaf_iff_of_forall_exists.{u + 1, u}
    (fun W : T.ProEt ↦ IsAffine W.left ∧
      (Scheme.ProEt.topology T).IsWeaklyContractible.{u + 1} W)
    (fun V ↦ Scheme.ProEt.exists_isWeaklyContractible_cover V)]
  exact ⟨fun h W hW hW' ↦ h W ⟨hW, hW'⟩, fun h W hW ↦ h W hW.1 hW.2⟩

/-- **Detection of acyclicity** (Stacks 0947 (1), 0990): a complex of sheaves of `Λ`-modules on
the small pro-étale site is acyclic if and only if its sections over every affine weakly
contractible object form an acyclic complex of `Λ`-modules. -/
@[stacks 0947]
theorem acyclic_iff_forall_isWeaklyContractible
    (K : CochainComplex (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} Λ)) ℤ) :
    K.Acyclic ↔ ∀ W : T.ProEt, IsAffine W.left →
      (Scheme.ProEt.topology T).IsWeaklyContractible.{u + 1} W →
        (((sheafToPresheaf _ _ ⋙ (evaluation _ _).obj (op W)).mapHomologicalComplex _).obj
          K).Acyclic := by
  have h (n : ℤ) := GrothendieckTopology.exact_iff_of_forall_exists.{u + 1, u}
    (fun W : T.ProEt ↦ IsAffine W.left ∧
      (Scheme.ProEt.topology T).IsWeaklyContractible.{u + 1} W)
    (fun V ↦ Scheme.ProEt.exists_isWeaklyContractible_cover V) (fun _ hW ↦ hW.2) (K.sc n)
  exact ⟨fun hK W hW hW' n ↦ (h n).1 (hK n) W ⟨hW, hW'⟩,
    fun hK n ↦ (h n).2 fun W hW ↦ hK W hW.1 hW.2 n⟩

end ProEtale

end AlgebraicGeometry
