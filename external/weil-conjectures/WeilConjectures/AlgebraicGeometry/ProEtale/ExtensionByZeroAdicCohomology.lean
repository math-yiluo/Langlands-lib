/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.IntegralAdicCohomology
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Mono

/-!
# Integral `ℓ`-adic cohomology of an extension by zero

Let `j : U ⟶ T` be an open immersion of schemes and `p` a prime (in practice `ℓ`). This file
develops, for the pro-étale cohomology of the extensions by zero
`Hⁿ(T, j_! ℤ_p) = Hⁿ(T_proét, j_! C(-, ℤ_p))`
(`AlgebraicGeometry.ProEtale.CompactIntegralAdicH`) and
`Hⁿ(T, j_! ℤ/pᵐ) = Hⁿ(T_proét, j_! C(-, ℤ_p / pᵐ))`
(`AlgebraicGeometry.ProEtale.CompactFiniteAdicH`), the lattice theory that
`WeilConjectures.AlgebraicGeometry.ProEtale.IntegralAdicCohomology` develops for the constant
sheaves. When `T` is proper over an algebraically closed field these are the compactly
supported cohomology groups of `U`; the results feed the `ℚ̄_ℓ` stage of the compactly
supported case of degreewise duality over fields.

* the **Bockstein sequence**: the extension by zero `j_!` is exact, so it maps the Bockstein
  sequence `0 ⟶ ℤ_p --pᵐ--> ℤ_p ⟶ ℤ/pᵐ ⟶ 0` to a short exact sequence, whence
  `AlgebraicGeometry.ProEtale.exists_eq_pow_smul_of_compactReduction_eq_zero` and
  `AlgebraicGeometry.ProEtale.pow_smul_mem_range_compactReduction`;
* **separation** and **finite generation**
  (`AlgebraicGeometry.ProEtale.eq_zero_of_forall_compactReduction_eq_zero`,
  `AlgebraicGeometry.ProEtale.module_finite_compactIntegralAdicH`), from the fact that
  `j_! C(-, ℤ_p)` is the limit of the tower `j_! C(-, ℤ/pᵐ)`, for `j` quasi-compact;
* **compatible lifts** (`AlgebraicGeometry.ProEtale.exists_compactReduction_eq`).

## Implementation details

The limit statement is an instance of a general fact: the extension by zero along a
quasi-compact open immersion preserves sequential limits of abelian pro-étale sheaves
(`AlgebraicGeometry.ProEtale.isLimitMapConeOpenImmersionLowerShriek`). A compatible family of
sections of the `j_! Fₖ` over `V` lifts on the part `V ×_T U` of `V` over `U`; over the
complement, the `k`-th section vanishes on a cover, and the limit of the resulting tower of
covers (`AlgebraicGeometry.Scheme.AffineProEt.seqLimit`), whose points are described by
`AlgebraicGeometry.Scheme.AffineProEt.exists_seqLimitπ_eq`, is a weakly étale `K ⟶ V` covering
the complement on which all sections vanish.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite Abelian PadicInt

namespace PrimeSpectrum

section Compatible

local instance : PreservesFilteredColimitsOfSize.{0, 0} (forget CommRingCat.{u}) :=
  instPreservesFilteredColimitsOfSizeCommRingCatForgetRingHomCarrier_weilConjectures.{u}

variable (G : ℕ ⥤ CommRingCat.{u}) (q : ∀ n, PrimeSpectrum (G.obj n))
  (hq : ∀ n, comap (G.map (homOfLE n.le_succ)).hom (q (n + 1)) = q n)

include hq in
lemma comap_eq_of_compatible {m n : ℕ} (h : m ≤ n) :
    comap (G.map (homOfLE h)).hom (q n) = q m := by
  induction n, h using Nat.le_induction with
  | base => simp
  | succ n hmn ih =>
    have : homOfLE (hmn.trans n.le_succ) = homOfLE hmn ≫ homOfLE n.le_succ := rfl
    rw [this, Functor.map_comp, CommRingCat.hom_comp, comap_comp_apply, hq, ih]

include hq in
lemma map_mem_iff_of_compatible {m n : ℕ} (h : m ≤ n) (y : G.obj m) :
    G.map (homOfLE h) y ∈ (q n).asIdeal ↔ y ∈ (q m).asIdeal := by
  rw [← comap_eq_of_compatible G q hq h]
  rfl

include hq in
lemma mem_iff_of_colimit_ι_eq {m n : ℕ} (y : G.obj m) (z : G.obj n)
    (h : colimit.ι G m y = colimit.ι G n z) : y ∈ (q m).asIdeal ↔ z ∈ (q n).asIdeal := by
  obtain ⟨k, f, g, hk⟩ := (Concrete.colimit_rep_eq_iff_exists G y z).1 h
  rw [← map_mem_iff_of_compatible G q hq (leOfHom f) y,
    ← map_mem_iff_of_compatible G q hq (leOfHom g) z]
  exact Iff.of_eq (congrArg (· ∈ (q k).asIdeal) hk)

/-- The ideal of `colim G` of the elements represented by an element of some `qₙ`, for a
compatible sequence of primes `qₙ` of the `G n`. -/
noncomputable def colimitIdealOfCompatible : Ideal (colimit G : CommRingCat) where
  carrier := {x | ∃ n y, colimit.ι G n y = x ∧ y ∈ (q n).asIdeal}
  add_mem' := by
    rintro _ _ ⟨m, y, rfl, hy⟩ ⟨n, z, rfl, hz⟩
    refine ⟨max m n, G.map (homOfLE (le_max_left m n)) y + G.map (homOfLE (le_max_right m n)) z,
      ?_, add_mem ((map_mem_iff_of_compatible G q hq _ y).2 hy)
        ((map_mem_iff_of_compatible G q hq _ z).2 hz)⟩
    rw [map_add, ← CommRingCat.comp_apply, ← CommRingCat.comp_apply, colimit.w, colimit.w]
  zero_mem' := ⟨0, 0, map_zero _, zero_mem _⟩
  smul_mem' := by
    rintro c _ ⟨n, z, rfl, hz⟩
    obtain ⟨m, y, rfl⟩ := Concrete.colimit_exists_rep G c
    refine ⟨max m n, G.map (homOfLE (le_max_left m n)) y * G.map (homOfLE (le_max_right m n)) z,
      ?_, Ideal.mul_mem_left _ _ ((map_mem_iff_of_compatible G q hq _ z).2 hz)⟩
    rw [map_mul, ← CommRingCat.comp_apply, ← CommRingCat.comp_apply, colimit.w, colimit.w,
      smul_eq_mul]

include hq in
lemma ι_mem_colimitIdealOfCompatible_iff (n : ℕ) (y : G.obj n) :
    colimit.ι G n y ∈ colimitIdealOfCompatible G q hq ↔ y ∈ (q n).asIdeal :=
  ⟨fun ⟨_, z, hz, hz'⟩ ↦ (mem_iff_of_colimit_ι_eq G q hq z y hz).1 hz', fun h ↦ ⟨n, y, rfl, h⟩⟩

include hq in
lemma isPrime_colimitIdealOfCompatible : (colimitIdealOfCompatible G q hq).IsPrime where
  ne_top' := by
    rw [Ne, Ideal.eq_top_iff_one, ← map_one (colimit.ι G 0).hom,
      ι_mem_colimitIdealOfCompatible_iff]
    exact fun h ↦ (q 0).isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h)
  mem_or_mem' := by
    intro a b hab
    obtain ⟨m, y, rfl⟩ := Concrete.colimit_exists_rep G a
    obtain ⟨n, z, rfl⟩ := Concrete.colimit_exists_rep G b
    rw [← colimit.w G (homOfLE (le_max_left m n)), ← colimit.w G (homOfLE (le_max_right m n)),
      CommRingCat.comp_apply, CommRingCat.comp_apply, ← map_mul,
      ι_mem_colimitIdealOfCompatible_iff] at hab
    rw [← colimit.w G (homOfLE (le_max_left m n)), ← colimit.w G (homOfLE (le_max_right m n)),
      CommRingCat.comp_apply, CommRingCat.comp_apply, ι_mem_colimitIdealOfCompatible_iff,
      ι_mem_colimitIdealOfCompatible_iff]
    exact (q _).isPrime.mem_or_mem hab

include hq in
/-- **Points of the spectrum of a sequential colimit.** A compatible sequence of primes `qₙ` of
the rings `G n` of a sequence comes from a prime of `colim G`. -/
theorem exists_comap_colimit_ι_eq :
    ∃ P : PrimeSpectrum (colimit G : CommRingCat), ∀ n, comap (colimit.ι G n).hom P = q n :=
  ⟨⟨colimitIdealOfCompatible G q hq, isPrime_colimitIdealOfCompatible G q hq⟩, fun n ↦
    PrimeSpectrum.ext (Ideal.ext fun y ↦ ι_mem_colimitIdealOfCompatible_iff G q hq n y)⟩

end Compatible

end PrimeSpectrum

namespace AlgebraicGeometry.Scheme.AffineProEt

variable {S : Scheme.{u}} {W : ℕ → S.AffineProEt} {π : ∀ n, W (n + 1) ⟶ W n}

/-- **Points of a sequential limit** in the affine pro-étale site: a compatible sequence of
points `xₙ` of the `Wₙ` comes from a point of `W_∞ = Spec (colim Γ(Wₙ))`. -/
theorem exists_seqLimitπ_eq (x : ∀ n, (W n).left)
    (hx : ∀ n, (π n).left.base (x (n + 1)) = x n) :
    ∃ y : (seqLimit W π).left, ∀ n, (seqLimitπ W π n).left.base y = x n := by
  let q (n : ℕ) : PrimeSpectrum Γ((W n).left, ⊤) := (W n).left.isoSpec.hom.base (x n)
  have hq (n : ℕ) : PrimeSpectrum.comap ((ringSeq W π).map (homOfLE n.le_succ)).hom (q (n + 1)) =
      q n := by
    rw [ringSeq_map_succ]
    change (Spec.map (π n).left.appTop).base ((W (n + 1)).left.isoSpec.hom.base (x (n + 1))) = _
    rw [← Scheme.Hom.comp_apply, Scheme.isoSpec_hom_naturality, Scheme.Hom.comp_apply, hx]
  obtain ⟨P, hP⟩ := PrimeSpectrum.exists_comap_colimit_ι_eq (ringSeq W π) q hq
  refine ⟨P, fun n ↦ ?_⟩
  change ((W n).left.isoSpec.inv).base ((Spec.map (colimit.ι (ringSeq W π) n)).base P) = x n
  change ((W n).left.isoSpec.inv).base (PrimeSpectrum.comap (colimit.ι (ringSeq W π) n).hom P) = _
  rw [hP n, ← Scheme.Hom.comp_apply, Iso.hom_inv_id]
  rfl

end AlgebraicGeometry.Scheme.AffineProEt

namespace AlgebraicGeometry.ProEtale

open Scheme

section ExtensionByZeroLimit

variable {U T : Scheme.{u}} (j : U ⟶ T) [IsOpenImmersion j]

-- the instance search for the sections of the sheafified Kan extension is slow
/-- **A section of an extension by zero vanishes on a cover of the complement.** For a section
`r` of `j_! G` over an object `B` of the affine pro-étale site, there is a morphism `B' ⟶ B` of
the affine pro-étale site along which `r` vanishes and whose image contains every point of `B`
lying over the complement of `U`. Indeed `r` locally comes from the presheaf extension by zero,
whose sections over objects not factoring through `U` vanish; the members of a finite
jointly surjective family on which `r` vanishes are collected into a single disjoint union. -/
lemma exists_map_eq_zero_openImmersionLowerShriek_of_affineProEt
    (G : Sheaf (ProEt.topology U) AddCommGrpCat.{u + 1}) (B : T.AffineProEt)
    (r : ToType (((j)_!open[AddCommGrpCat.{u + 1}].obj G).obj.obj
      (op ((AffineProEt.toProEt T).obj B)))) :
    ∃ (B' : T.AffineProEt) (π : B' ⟶ B),
      ((j)_!open[AddCommGrpCat.{u + 1}].obj G).obj.map ((AffineProEt.toProEt T).map π).op r =
        0 ∧ ∀ x : B.left, B.hom.base x ∉ Set.range j.base → x ∈ Set.range π.left.base := by
  let H := (j)_!open[AddCommGrpCat.{u + 1}].obj G
  set L := openImmersionLocalization j
  let R : Sieve ((AffineProEt.toProEt T).obj B) :=
    { arrows := fun W f ↦ Set.range W.hom.base ⊆ Set.range j.base ∨ H.obj.map f.op r = 0
      downward_closed := by
        rintro W W' f (hf | hf) g
        · left
          rintro _ ⟨y, rfl⟩
          refine hf ⟨g.left.base y, ?_⟩
          rw [← MorphismProperty.Over.w g]
          rfl
        · right
          rw [op_comp, Functor.map_comp, ConcreteCategory.comp_apply, hf, map_zero] }
  have hR : R ∈ ProEt.topology T ((AffineProEt.toProEt T).obj B) := by
    have : Presheaf.IsLocallySurjective (ProEt.topology T)
        (toSheafify (ProEt.topology T) (L.op.leftKanExtension G.obj)) :=
      Presheaf.isLocallySurjective_toSheafify' (J := ProEt.topology T) _
    refine GrothendieckTopology.superset_covering _ ?_ (Presheaf.imageSieve_mem
      (ProEt.topology T) (toSheafify (ProEt.topology T) (L.op.leftKanExtension G.obj)) r)
    rintro W f ⟨t, ht⟩
    by_cases hc : IsEmpty (CostructuredArrow L.op (op W))
    · right
      have hI := (isColimitEquivIsInitialOfIsEmpty _ _).1
        (L.op.isPointwiseLeftKanExtensionLeftKanExtensionUnit G.obj (op W))
      have : Subsingleton (ToType ((L.op.leftKanExtension G.obj).obj (op W))) :=
        AddCommGrpCat.subsingleton_of_isZero hI.isZero
      change ConcreteCategory.hom ((sheafify (ProEt.topology T)
        (L.op.leftKanExtension G.obj)).map f.op) r = 0
      rw [← ht, Subsingleton.elim t 0, map_zero]
    · left
      obtain ⟨c⟩ := not_isEmpty_iff.1 hc
      rintro _ ⟨y, rfl⟩
      refine ⟨(c.left.unop.hom).base ((c.hom.unop.left).base y), ?_⟩
      have h₁ := MorphismProperty.Over.w c.hom.unop
      change (c.hom.unop.left ≫ c.left.unop.hom ≫ j) = W.hom at h₁
      rw [← h₁]
      rfl
  have hRp : R.functorPullback (AffineProEt.toProEt T) ∈ AffineProEt.topology T B :=
    Functor.mem_restrictedTopology_of_functorPushforward_mem
      (Functor.IsCoverDense.functorPullback_pushforward_covering ⟨R, hR⟩)
  obtain ⟨ι, _, V, f, hRf, hsurj⟩ :=
    AffineProEt.exists_finite_jointly_surjective_of_mem_topology hRp
  let ι' := {i : ι // H.obj.map ((AffineProEt.toProEt T).map (f i)).op r = 0}
  let V' (i : ι') : T.AffineProEt := V i.1
  let f' (i : ι') : V' i ⟶ B := f i.1
  refine ⟨AffineProEt.sigmaCover V' f', AffineProEt.sigmaCoverπ V' f', ?_, fun x hx ↦ ?_⟩
  · let Fa : T.AffineProEtᵒᵖ ⥤ Type (u + 1) :=
      (AffineProEt.toProEt T).op ⋙ H.obj ⋙ forget AddCommGrpCat.{u + 1}
    have hFa : Presheaf.IsSheaf (AffineProEt.topology T) Fa :=
      ((sheafCompose (AffineProEt.topology T) (forget AddCommGrpCat.{u + 1})).obj
        (((AffineProEt.toProEt T).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
          (AffineProEt.topology T) (ProEt.topology T)).obj H)).property
    refine AffineProEt.sigmaCover_ext V' f' hFa (z' := (0 : ToType (H.obj.obj
      (op ((AffineProEt.toProEt T).obj (AffineProEt.sigmaCover V' f')))))) fun i ↦ ?_
    change H.obj.map ((AffineProEt.toProEt T).map (AffineProEt.sigmaCoverι V' f' i)).op
        (H.obj.map ((AffineProEt.toProEt T).map (AffineProEt.sigmaCoverπ V' f')).op r) =
      H.obj.map ((AffineProEt.toProEt T).map (AffineProEt.sigmaCoverι V' f' i)).op 0
    rw [map_zero, ← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp,
      ← Functor.map_comp, AffineProEt.sigmaCoverι_π]
    exact i.2
  · obtain ⟨i, y, rfl⟩ := hsurj x
    have hi : H.obj.map ((AffineProEt.toProEt T).map (f i)).op r = 0 := by
      refine (hRf i).resolve_left fun h ↦ hx ?_
      obtain ⟨z, hz⟩ := h ⟨y, rfl⟩
      refine ⟨z, hz.trans ?_⟩
      change (V i).hom.base y = _
      rw [← MorphismProperty.Over.w (f i)]
      rfl
    refine ⟨(AffineProEt.sigmaCoverι V' f' ⟨i, hi⟩).left.base y, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← MorphismProperty.Comma.comp_left,
      AffineProEt.sigmaCoverι_π]


omit [IsOpenImmersion j] in
/-- Naturality of a morphism of abelian sheaves, on sections. -/
lemma sheafHom_app_map_apply {H H' : Sheaf (ProEt.topology T) AddCommGrpCat.{u + 1}} (φ : H ⟶ H')
    {V W : T.ProEt} (h : W ⟶ V) (x : ToType (H.obj.obj (op V))) :
    φ.hom.app (op W) (H.obj.map h.op x) = H'.obj.map h.op (φ.hom.app (op V) x) := by
  rw [← ConcreteCategory.comp_apply, φ.hom.naturality, ConcreteCategory.comp_apply]

variable {j} {F : ℕᵒᵖ ⥤ Sheaf (ProEt.topology U) AddCommGrpCat.{u + 1}} {c : Cone F}

variable (c) in
/-- The sieve of the morphisms `W ⟶ V` along which a compatible family of sections `sₖ` of the
`j_! Fₖ` lifts to a section of `j_! (lim Fₖ)`. -/
def liftSieve {V : T.ProEt}
    (s : ∀ k, ToType (((j)_!open[AddCommGrpCat.{u + 1}].obj (F.obj k)).obj.obj (op V))) :
    Sieve V where
  arrows W g := ∃ t : ToType (((j)_!open[AddCommGrpCat.{u + 1}].obj c.pt).obj.obj (op W)),
    ∀ k, ((j)_!open[AddCommGrpCat.{u + 1}].map (c.π.app k)).hom.app (op W) t =
      ((j)_!open[AddCommGrpCat.{u + 1}].obj (F.obj k)).obj.map g.op (s k)
  downward_closed := by
    rintro W W' g ⟨t, ht⟩ h
    refine ⟨((j)_!open[AddCommGrpCat.{u + 1}].obj c.pt).obj.map h.op t, fun k ↦ ?_⟩
    refine (sheafHom_app_map_apply _ _ _).trans ?_
    rw [ht, op_comp, Functor.map_comp, ConcreteCategory.comp_apply]

/-- Sections of an extension by zero over an object factoring through `U` are sections of the
sheaf: the unit of `j_! ⊣ j^*` is an isomorphism. -/
lemma bijective_openImmersionLowerShriekAdjunction_unit_app
    (G : Sheaf (ProEt.topology U) AddCommGrpCat.{u + 1}) (b : U.ProEt) :
    Function.Bijective
      (((openImmersionLowerShriekAdjunction AddCommGrpCat.{u + 1} j).unit.app G).hom.app
        (op b)) := by
  have : IsIso ((openImmersionLowerShriekAdjunction AddCommGrpCat.{u + 1} j).unit.app G) :=
    inferInstance
  have : IsIso ((sheafToPresheaf _ _).map
      ((openImmersionLowerShriekAdjunction AddCommGrpCat.{u + 1} j).unit.app G)) :=
    inferInstance
  have : IsIso (((openImmersionLowerShriekAdjunction AddCommGrpCat.{u + 1} j).unit.app
      G).hom.app (op b)) :=
    NatIso.isIso_app_of_isIso ((sheafToPresheaf _ _).map
      ((openImmersionLowerShriekAdjunction AddCommGrpCat.{u + 1} j).unit.app G)) (op b)
  exact ConcreteCategory.bijective_of_isIso _

variable [QuasiCompact j]

/-- The key step of `AlgebraicGeometry.ProEtale.isLimitMapConeOpenImmersionLowerShriek`, over
an object of the affine pro-étale site. -/
lemma liftSieve_mem_of_affineProEt (hc : IsLimit c) (X : T.AffineProEt)
    (s : ∀ k, ToType (((j)_!open[AddCommGrpCat.{u + 1}].obj (F.obj k)).obj.obj
      (op ((AffineProEt.toProEt T).obj X))))
    (hs : ∀ ⦃k k' : ℕᵒᵖ⦄ (f : k ⟶ k'),
      ((j)_!open[AddCommGrpCat.{u + 1}].map (F.map f)).hom.app _ (s k) = s k') :
    liftSieve c s ∈ ProEt.topology T ((AffineProEt.toProEt T).obj X) := by
  let E := (j)_!open[AddCommGrpCat.{u + 1}]
  let P := AffineProEt.toProEt T
  let res (k : ℕ) {B : T.AffineProEt} (b : B ⟶ X) : ToType ((E.obj (F.obj (op k))).obj.obj
      (op (P.obj B))) := (E.obj (F.obj (op k))).obj.map (P.map b).op (s (op k))
  -- the tower of objects along which the `sₖ` successively vanish
  choose B' π hπ0 hπpt using fun (k : ℕ) (B : T.AffineProEt) r ↦
    exists_map_eq_zero_openImmersionLowerShriek_of_affineProEt j (F.obj (op k)) B r
  let seq : ℕ → Σ B : T.AffineProEt, (B ⟶ X) := fun n ↦ Nat.rec ⟨X, 𝟙 X⟩
    (fun k p ↦ ⟨B' k p.1 (res k p.2), π k p.1 (res k p.2) ≫ p.2⟩) n
  let πs (k : ℕ) : (seq (k + 1)).1 ⟶ (seq k).1 := π k (seq k).1 (res k (seq k).2)
  have hseq (k : ℕ) : (seq (k + 1)).2 = πs k ≫ (seq k).2 := rfl
  have hzero (k : ℕ) : (E.obj (F.obj (op k))).obj.map (P.map (πs k)).op
      ((E.obj (F.obj (op k))).obj.map (P.map (seq k).2).op (s (op k))) = 0 :=
    hπ0 k _ _
  let K := AffineProEt.seqLimit (fun k ↦ (seq k).1) πs
  let pK := AffineProEt.seqLimitπ (fun k ↦ (seq k).1) πs
  let κ : K ⟶ X := pK 0 ≫ (seq 0).2
  have hκ (k : ℕ) : pK k ≫ (seq k).2 = κ := by
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [hseq, ← Category.assoc, AffineProEt.seqLimitπ_comp, ih]
  have hsK (k : ℕ) : (E.obj (F.obj (op k))).obj.map (P.map κ).op (s (op k)) = 0 := by
    rw [← hκ (k + 1), hseq]
    simp only [Functor.map_comp, op_comp, ConcreteCategory.comp_apply, hzero, map_zero]
  -- the points over the complement of `U` lift to `K`
  have hKpt (x : X.left) (hx : X.hom.base x ∉ Set.range j.base) :
      x ∈ Set.range κ.left.base := by
    have step (k : ℕ) (y : (seq k).1.left) (hy : (seq k).1.hom.base y ∉ Set.range j.base) :
        ∃ z : (seq (k + 1)).1.left, (πs k).left.base z = y ∧
          (seq (k + 1)).1.hom.base z ∉ Set.range j.base := by
      obtain ⟨z, hz⟩ := hπpt k _ _ y hy
      refine ⟨z, hz, fun h ↦ hy ?_⟩
      have hw : (seq k).1.hom.base y = (seq (k + 1)).1.hom.base z := by
        rw [← hz]
        exact congrArg (fun φ : (seq (k + 1)).1.left ⟶ T ↦ φ.base z)
          (MorphismProperty.Over.w (πs k))
      rw [hw]
      exact h
    choose z hz hz' using step
    let xs : ∀ k, {y : (seq k).1.left // (seq k).1.hom.base y ∉ Set.range j.base} :=
      fun n ↦ Nat.rec ⟨x, hx⟩ (fun k y ↦ ⟨z k y.1 y.2, hz' k y.1 y.2⟩) n
    obtain ⟨y, hy⟩ := AffineProEt.exists_seqLimitπ_eq (W := fun k ↦ (seq k).1) (π := πs)
      (fun k ↦ (xs k).1) fun k ↦ hz k (xs k).1 (xs k).2
    exact ⟨y, hy 0⟩
  -- the part over `U`
  let V := P.obj X
  let b : U.ProEt := (MorphismProperty.Over.pullback @WeaklyEtale ⊤ j).obj V
  let Lb : T.ProEt := (openImmersionLocalization j).obj b
  let ε : Lb ⟶ V := MorphismProperty.Over.homMk (pullback.fst V.hom j) pullback.condition trivial
  have hε : (liftSieve c s).arrows ε := by
    let η := (openImmersionLowerShriekAdjunction AddCommGrpCat.{u + 1} j).unit
    have hb (G) := bijective_openImmersionLowerShriekAdjunction_unit_app (j := j) G b
    let y (k : ℕᵒᵖ) : ToType ((E.obj (F.obj k)).obj.obj (op Lb)) :=
      (E.obj (F.obj k)).obj.map ε.op (s k)
    choose σ hσ using fun k ↦ (hb (F.obj k)).2 (y k)
    have hηnat {G G' : Sheaf (ProEt.topology U) AddCommGrpCat.{u + 1}} (φ : G ⟶ G')
        (a : ToType (G.obj.obj (op b))) :
        (E.map φ).hom.app (op Lb) ((η.app G).hom.app (op b) a) =
          (η.app G').hom.app (op b) (φ.hom.app (op b) a) := by
      have h := η.naturality φ
      have h' := congrArg (fun ψ ↦ ψ.hom.app (op b) a) h
      exact h'.symm
    have hσc : σ ∈ (F ⋙ sheafToPresheaf _ _ ⋙ (CategoryTheory.evaluation _ _).obj (op b) ⋙
        forget AddCommGrpCat.{u + 1}).sections := by
      intro k k' f
      refine (hb (F.obj k')).1 ?_
      change (η.app (F.obj k')).hom.app (op b) ((F.map f).hom.app (op b) (σ k)) = _
      rw [← hηnat, hσ, hσ]
      change (E.map (F.map f)).hom.app (op Lb) ((E.obj (F.obj k)).obj.map ε.op (s k)) =
        (E.obj (F.obj k')).obj.map ε.op (s k')
      refine (sheafHom_app_map_apply _ _ _).trans ?_
      rw [hs]
    have hlim := isLimitOfPreserves (sheafToPresheaf _ _ ⋙
      (CategoryTheory.evaluation _ _).obj (op b) ⋙ forget AddCommGrpCat.{u + 1}) hc
    obtain ⟨τ, hτ, -⟩ := (Types.isLimit_iff _).1 ⟨hlim⟩ σ hσc
    refine ⟨(η.app c.pt).hom.app (op b) τ, fun k ↦ ?_⟩
    refine (hηnat (c.π.app k) τ).trans ?_
    change (η.app (F.obj k)).hom.app (op b) ((c.π.app k).hom.app (op b) τ) = _
    rw [show (c.π.app k).hom.app (op b) τ = σ k from hτ k, hσ]
  -- the cover
  let Y : Bool → T.ProEt := fun i ↦ Bool.rec (P.obj K) Lb i
  let g : ∀ i, Y i ⟶ V := fun i ↦ Bool.rec (motive := fun i ↦ Y i ⟶ V) (P.map κ) ε i
  have hsurj (x : V.left) : ∃ i, x ∈ Set.range (g i).left.base := by
    by_cases hx : V.hom.base x ∈ Set.range j.base
    · obtain ⟨w, hw⟩ := hx
      obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback x w hw.symm
      exact ⟨true, z, hz⟩
    · obtain ⟨z, hz⟩ := hKpt x hx
      exact ⟨false, z, hz⟩
  let D : PreZeroHypercover V.left := ⟨Bool, fun i ↦ (Y i).left, fun i ↦ (g i).left⟩
  have : ∀ i, QuasiCompact (D.f i) := by
    rintro (_ | _)
    · change QuasiCompact κ.left
      infer_instance
    · change QuasiCompact (pullback.fst V.hom j)
      infer_instance
  have hD : QuasiCompactCover D :=
    ⟨fun {U} hU ↦ IsCompactOpenCovered.of_finite_of_isSpectralMap
      (fun i ↦ (D.f i).isSpectralMap) (fun x _ ↦ hsurj x) U.2 hU.isCompact⟩
  have hmem : D.presieve₀ ∈ Scheme.proetalePrecoverage V.left := by
    refine ⟨Scheme.presieve₀_mem_qcPrecoverage_iff.2 hD,
      (Scheme.ofArrows_mem_precoverage_iff (P := @WeaklyEtale)).2 ⟨hsurj, ?_⟩⟩
    rintro (_ | _)
    · change WeaklyEtale κ.left
      infer_instance
    · change WeaklyEtale (pullback.fst V.hom j)
      infer_instance
  rw [ProEt.mem_topology_iff]
  refine ⟨Presieve.ofArrows Y g, ?_, ?_⟩
  · rw [ProEt.mem_precoverage_iff, Presieve.map_ofArrows]
    exact hmem
  · rintro _ _ ⟨(_ | _)⟩
    · exact ⟨0, fun k ↦ by rw [map_zero]; exact (hsK (unop k)).symm⟩
    · exact hε

/-- Every compatible family of sections of the `j_! Fₖ` lifts locally to `j_! (lim Fₖ)`. -/
lemma liftSieve_mem (hc : IsLimit c) {V : T.ProEt}
    (s : ∀ k, ToType (((j)_!open[AddCommGrpCat.{u + 1}].obj (F.obj k)).obj.obj (op V)))
    (hs : ∀ ⦃k k' : ℕᵒᵖ⦄ (f : k ⟶ k'),
      ((j)_!open[AddCommGrpCat.{u + 1}].map (F.map f)).hom.app _ (s k) = s k') :
    liftSieve c s ∈ ProEt.topology T V := by
  let E := (j)_!open[AddCommGrpCat.{u + 1}]
  refine (ProEt.topology T).transitive
    ((AffineProEt.toProEt T).is_cover_of_isCoverDense (ProEt.topology T) V) _ ?_
  rintro W f ⟨⟨X, lift, m, fac⟩⟩
  let s' (k : ℕᵒᵖ) := (E.obj (F.obj k)).obj.map m.op (s k)
  have hs' ⦃k k' : ℕᵒᵖ⦄ (f : k ⟶ k') : (E.map (F.map f)).hom.app _ (s' k) = s' k' := by
    change (E.map (F.map f)).hom.app _ ((E.obj (F.obj k)).obj.map m.op (s k)) = _
    refine (sheafHom_app_map_apply _ _ _).trans ?_
    rw [hs]
  refine (ProEt.topology T).superset_covering ?_ ((ProEt.topology T).pullback_stable lift
    (liftSieve_mem_of_affineProEt hc X s' hs'))
  rintro W' h ⟨t, ht⟩
  refine ⟨t, fun k ↦ (ht k).trans ?_⟩
  change (E.obj (F.obj k)).obj.map (h ≫ lift).op ((E.obj (F.obj k)).obj.map m.op (s k)) = _
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, Category.assoc, fac]

omit [QuasiCompact j] in
/-- Sections of `j_! (lim Fₖ)` are determined by their images in the `j_! Fₖ`: the comparison
`j_! ⟶ j_*` is a monomorphism and `j_*` preserves limits. -/
lemma eq_of_forall_openImmersionLowerShriek_map_eq (hc : IsLimit c) {V : T.ProEt}
    {t t' : ToType (((j)_!open[AddCommGrpCat.{u + 1}].obj c.pt).obj.obj (op V))}
    (h : ∀ k, ((j)_!open[AddCommGrpCat.{u + 1}].map (c.π.app k)).hom.app (op V) t =
      ((j)_!open[AddCommGrpCat.{u + 1}].map (c.π.app k)).hom.app (op V) t') : t = t' := by
  let ψ := openImmersionLowerShriekToLowerStar AddCommGrpCat.{u + 1} j
  have : Mono ((sheafToPresheaf _ _).map (ψ.app c.pt)) := inferInstance
  have : Mono ((ψ.app c.pt).hom.app (op V)) :=
    inferInstanceAs (Mono (((sheafToPresheaf _ _).map (ψ.app c.pt)).app (op V)))
  refine (AddCommGrpCat.mono_iff_injective _).1 this ?_
  have hlim := isLimitOfPreserves ((j)_*[AddCommGrpCat.{u + 1}] ⋙ sheafToPresheaf _ _ ⋙
    (CategoryTheory.evaluation _ _).obj (op V)) hc
  refine Concrete.isLimit_ext _ hlim _ _ fun k ↦ ?_
  have hn (a : ToType (((j)_!open[AddCommGrpCat.{u + 1}].obj c.pt).obj.obj (op V))) :
      ((j)_*[AddCommGrpCat.{u + 1}].map (c.π.app k)).hom.app (op V) ((ψ.app c.pt).hom.app
        (op V) a) = (ψ.app (F.obj k)).hom.app (op V)
          (((j)_!open[AddCommGrpCat.{u + 1}].map (c.π.app k)).hom.app (op V) a) :=
    (congrArg (fun φ ↦ φ.hom.app (op V) a) (ψ.naturality (c.π.app k))).symm
  change ((j)_*[AddCommGrpCat.{u + 1}].map (c.π.app k)).hom.app (op V) _ =
    ((j)_*[AddCommGrpCat.{u + 1}].map (c.π.app k)).hom.app (op V) _
  rw [hn, hn, h]

/-- **The extension by zero preserves sequential limits.** For a quasi-compact open immersion
`j : U ⟶ T`, the extension by zero `j_!` of abelian pro-étale sheaves maps a limit of a tower
`⋯ ⟶ F₁ ⟶ F₀` to a limit. A compatible family of sections of the `j_! Fₖ` over `V` lifts on the
part of `V` over `U`, and vanishes on a weakly étale `K ⟶ V` covering the part over the
complement of `U`: `K` is the limit of a tower of covers on which the `sₖ` successively vanish
(`AlgebraicGeometry.Scheme.AffineProEt.seqLimit`). -/
noncomputable def isLimitMapConeOpenImmersionLowerShriek (hc : IsLimit c) :
    IsLimit ((j)_!open[AddCommGrpCat.{u + 1}].mapCone c) := by
  let E := (j)_!open[AddCommGrpCat.{u + 1}]
  refine isLimitOfReflects (sheafToPresheaf _ _) (evaluationJointlyReflectsLimits _ fun V ↦ ?_)
  refine isLimitOfReflects (CategoryTheory.forget AddCommGrpCat.{u + 1}) ?_
  refine Classical.choice ((Types.isLimit_iff _).2 fun s hs ↦ ?_)
  let s' (k : ℕᵒᵖ) : ToType ((E.obj (F.obj k)).obj.obj (op V.unop)) := s k
  have hs' ⦃k k' : ℕᵒᵖ⦄ (f : k ⟶ k') : (E.map (F.map f)).hom.app _ (s' k) = s' k' := hs f
  have hS := liftSieve_mem hc s' hs'
  let P := (E.obj c.pt).obj ⋙ forget AddCommGrpCat.{u + 1}
  have hP : Presieve.IsSheaf (ProEt.topology T) P :=
    (isSheaf_iff_isSheaf_of_type _ _).1 (Presheaf.isSheaf_comp_of_isSheaf _ (E.obj c.pt).obj
      (forget AddCommGrpCat.{u + 1}) (E.obj c.pt).property)
  let x : Presieve.FamilyOfElements P (liftSieve c s').arrows := fun _ _ hg ↦ hg.choose
  have hx : x.Compatible := by
    rw [Presieve.compatible_iff_sieveCompatible]
    intro W W' g h hg
    refine eq_of_forall_openImmersionLowerShriek_map_eq hc fun k ↦ ?_
    rw [(liftSieve c s').downward_closed hg h |>.choose_spec k]
    change _ = (E.map (c.π.app k)).hom.app _ ((E.obj c.pt).obj.map h.op hg.choose)
    refine Eq.trans ?_ (sheafHom_app_map_apply _ _ _).symm
    rw [hg.choose_spec k, op_comp, Functor.map_comp,
      ConcreteCategory.comp_apply]
  obtain ⟨t, ht, -⟩ := hP _ hS x hx
  have himg (k : ℕᵒᵖ) : (E.map (c.π.app k)).hom.app (op V.unop) t = s' k := by
    have hsep : Presieve.IsSeparatedFor ((E.obj (F.obj k)).obj ⋙ forget AddCommGrpCat.{u + 1})
        (liftSieve c s').arrows :=
      ((isSheaf_iff_isSheaf_of_type _ _).1 (Presheaf.isSheaf_comp_of_isSheaf _
        (E.obj (F.obj k)).obj (forget AddCommGrpCat.{u + 1}) (E.obj (F.obj k)).property) _
          hS).isSeparatedFor
    refine hsep.ext fun W g hg ↦ ?_
    change (E.obj (F.obj k)).obj.map g.op ((E.map (c.π.app k)).hom.app _ t) =
      (E.obj (F.obj k)).obj.map g.op (s' k)
    refine (sheafHom_app_map_apply _ _ _).symm.trans ?_
    rw [← hg.choose_spec k]
    congr 1
    exact ht g hg
  exact ⟨t, himg, fun t' ht' ↦ eq_of_forall_openImmersionLowerShriek_map_eq hc fun k ↦
    (ht' k).trans (himg k).symm⟩

/-- **The extension by zero along a quasi-compact open immersion preserves sequential limits**
of abelian pro-étale sheaves. -/
instance preservesLimitsOfShape_openImmersionLowerShriek :
    PreservesLimitsOfShape ℕᵒᵖ ((j)_!open[AddCommGrpCat.{u + 1}]) :=
  ⟨fun {_} ↦ preservesLimit_of_preserves_limit_cone (limit.isLimit _)
    (isLimitMapConeOpenImmersionLowerShriek (limit.isLimit _))⟩

end ExtensionByZeroLimit

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale

section RingHom

variable {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
  {R : Type*} [Ring R]

/-- An additive functor maps an action `R →+* End X` of a ring on an object to an action on its
image. -/
@[simps]
def _root_.CategoryTheory.Functor.mapRingHom (G : C ⥤ D) [G.Additive] {X : C}
    (φ : R →+* End X) : R →+* End (G.obj X) where
  toFun r := .of (G.map (φ r).asHom)
  map_one' := by
    apply End.ext
    change G.map (φ 1).asHom = 𝟙 (G.obj X)
    rw [map_one, End.one_asHom]
    exact G.map_id X
  map_mul' r s := by
    apply End.ext
    simp only [map_mul, End.mul_asHom, Functor.map_comp]
  map_zero' := by
    apply End.ext
    simp only [map_zero, End.zero_asHom, Functor.map_zero]
  map_add' r s := by
    apply End.ext
    simp only [map_add, End.add_asHom, Functor.map_add]

end RingHom

variable {U T : Scheme.{u}} (j : U ⟶ T) [IsOpenImmersion j] (p : ℕ) [Fact p.Prime]

/-- The action of `ℤ_p` on `j_! C(-, ℤ_p)`. -/
noncomputable abbrev compactIntegralSmulRingHom :
    ℤ_[p] →+* End ((j)_!open[AddCommGrpCat.{u + 1}].obj (continuousSheaf U ℤ_[p])) :=
  (j)_!open[AddCommGrpCat.{u + 1}].mapRingHom (integralSmulRingHom U p)

/-- The action of `ℤ_p` on `j_! C(-, ℤ_p / pᵐ)`. -/
noncomputable abbrev compactFiniteSmulRingHom (m : ℕ) :
    ℤ_[p] →+* End ((j)_!open[AddCommGrpCat.{u + 1}].obj
      (continuousSheaf U (ℤ_[p] ⧸ (powOpenAddSubgroup p m : AddSubgroup ℤ_[p])))) :=
  (j)_!open[AddCommGrpCat.{u + 1}].mapRingHom (finiteSmulRingHom U p m)

/-- The integral `p`-adic pro-étale cohomology `Hⁿ(T, j_! ℤ_p) = Hⁿ(T_proét, j_! C(-, ℤ_p))` of
the extension by zero along an open immersion `j : U ⟶ T`, a `ℤ_p`-module. For `T` proper over
an algebraically closed field this is the compactly supported cohomology `Hⁿ_c(U, ℤ_p)`. -/
def CompactIntegralAdicH (n : ℕ) : Type (u + 1) :=
  Sheaf.H ((j)_!open[AddCommGrpCat.{u + 1}].obj (continuousSheaf U ℤ_[p])) n

noncomputable instance (n : ℕ) : AddCommGroup (CompactIntegralAdicH j p n) :=
  inferInstanceAs (AddCommGroup (Sheaf.H ((j)_!open[AddCommGrpCat.{u + 1}].obj
    (continuousSheaf U ℤ_[p])) n))

noncomputable instance (n : ℕ) : Module ℤ_[p] (CompactIntegralAdicH j p n) :=
  Ext.moduleOfRingHom (compactIntegralSmulRingHom j p) n

/-- The pro-étale cohomology `Hⁿ(T, j_! ℤ/pᵐ) = Hⁿ(T_proét, j_! C(-, ℤ_p / pᵐ))` of the
extension by zero along an open immersion `j : U ⟶ T`, a `ℤ_p`-module. -/
def CompactFiniteAdicH (m n : ℕ) : Type (u + 1) :=
  Sheaf.H ((j)_!open[AddCommGrpCat.{u + 1}].obj
    (continuousSheaf U (ℤ_[p] ⧸ (powOpenAddSubgroup p m : AddSubgroup ℤ_[p])))) n

noncomputable instance (m n : ℕ) : AddCommGroup (CompactFiniteAdicH j p m n) :=
  inferInstanceAs (AddCommGroup (Sheaf.H ((j)_!open[AddCommGrpCat.{u + 1}].obj
    (continuousSheaf U (ℤ_[p] ⧸ (powOpenAddSubgroup p m : AddSubgroup ℤ_[p])))) n))

noncomputable instance (m n : ℕ) : Module ℤ_[p] (CompactFiniteAdicH j p m n) :=
  Ext.moduleOfRingHom (compactFiniteSmulRingHom j p m) n

/-- The extension by zero `j_! C(-, ℤ_p) ⟶ j_! C(-, ℤ_p / pᵐ)` of the reduction. -/
noncomputable abbrev compactReductionSheafMap (m : ℕ) :
    (j)_!open[AddCommGrpCat.{u + 1}].obj (continuousSheaf U ℤ_[p]) ⟶
      (j)_!open[AddCommGrpCat.{u + 1}].obj
        (continuousSheaf U (ℤ_[p] ⧸ (powOpenAddSubgroup p m : AddSubgroup ℤ_[p]))) :=
  (j)_!open[AddCommGrpCat.{u + 1}].map (reductionSheafMap U p m)

lemma compactReductionSheafMap_comm (m : ℕ) (c : ℤ_[p]) :
    (compactIntegralSmulRingHom j p c).asHom ≫ compactReductionSheafMap j p m =
      compactReductionSheafMap j p m ≫ (compactFiniteSmulRingHom j p m c).asHom := by
  simp only [Functor.mapRingHom_apply_asHom, ← Functor.map_comp, reductionSheafMap_comm]

/-- The reduction `ρₘ : Hⁿ(T, j_! ℤ_p) ⟶ Hⁿ(T, j_! ℤ/pᵐ)`. -/
noncomputable def compactReduction (m n : ℕ) :
    CompactIntegralAdicH j p n →ₗ[ℤ_[p]] CompactFiniteAdicH j p m n :=
  Ext.postcompLinearMap (compactIntegralSmulRingHom j p) (compactFiniteSmulRingHom j p m)
    (compactReductionSheafMap j p m) (compactReductionSheafMap_comm j p m) n

lemma compactReduction_apply (m n : ℕ) (x : CompactIntegralAdicH j p n) :
    compactReduction j p m n x = Ext.comp (C := Sheaf (Scheme.ProEt.topology T)
      AddCommGrpCat.{u + 1}) x (Ext.mk₀ (compactReductionSheafMap j p m)) (add_zero n) :=
  rfl

/-- `pᵐ` kills `Hⁿ(T, j_! ℤ/pᵐ)`. -/
lemma pow_smul_compactFiniteAdicH (m n : ℕ) (y : CompactFiniteAdicH j p m n) :
    (p : ℤ_[p]) ^ m • y = 0 := by
  have h : finiteSmulRingHom U p m ((p : ℤ_[p]) ^ m) = 0 := by
    apply End.ext
    refine (continuousSheafMap_congr U fun x ↦ ?_).trans (continuousSheafMap_zero U)
    induction x using QuotientAddGroup.induction_on with
    | H a =>
      refine (QuotientAddGroup.eq_zero_iff _).2 ?_
      exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  change Ext.comp y (Ext.mk₀ ((j)_!open[AddCommGrpCat.{u + 1}].map
    (finiteSmulRingHom U p m ((p : ℤ_[p]) ^ m)).asHom)) (add_zero n) = 0
  rw [h, End.zero_asHom, Functor.map_zero, Ext.mk₀_zero, Ext.comp_zero]

/-- The extension by zero of the Bockstein short complex,
`j_! C(-, ℤ_p) --pᵐ--> j_! C(-, ℤ_p) ⟶ j_! C(-, ℤ_p / pᵐ)`. -/
noncomputable abbrev compactBocksteinShortComplex (m : ℕ) :
    ShortComplex (Sheaf (Scheme.ProEt.topology T) AddCommGrpCat.{u + 1}) :=
  (bocksteinShortComplex U p m).map (j)_!open[AddCommGrpCat.{u + 1}]

lemma shortExact_compactBocksteinShortComplex (m : ℕ) :
    (compactBocksteinShortComplex j p m).ShortExact :=
  (shortExact_bocksteinShortComplex U p m).map_of_exact _

/-- **Bockstein, first part.** The kernel of `ρₘ : Hⁿ(T, j_! ℤ_p) ⟶ Hⁿ(T, j_! ℤ/pᵐ)` is
`pᵐ Hⁿ(T, j_! ℤ_p)`. -/
theorem exists_eq_pow_smul_of_compactReduction_eq_zero (m n : ℕ)
    {x : CompactIntegralAdicH j p n} (hx : compactReduction j p m n x = 0) :
    ∃ x', x = (p : ℤ_[p]) ^ m • x' := by
  obtain ⟨x', hx'⟩ := Ext.covariant_sequence_exact₂ _
    (shortExact_compactBocksteinShortComplex j p m) (n := n) x hx
  exact ⟨x', hx'.symm⟩

/-- The connecting map `δ : Hⁿ(T, j_! ℤ/pᵐ) ⟶ Hⁿ⁺¹(T, j_! ℤ_p)` of the Bockstein sequence. -/
noncomputable def compactBocksteinδ (m n : ℕ) :
    CompactFiniteAdicH j p m n →+ CompactIntegralAdicH j p (n + 1) :=
  AddMonoidHom.mk' (fun y ↦ Ext.comp (C := Sheaf (Scheme.ProEt.topology T)
    AddCommGrpCat.{u + 1}) y (shortExact_compactBocksteinShortComplex j p m).extClass rfl)
    fun _ _ ↦ Ext.add_comp _ _ _ _

private lemma pow_smul_eq_nsmul_compactIntegral (n e : ℕ) (x : CompactIntegralAdicH j p n) :
    (p : ℤ_[p]) ^ e • x = (p ^ e) • x := by
  rw [← Ext.smul_natCast_eq_nsmul (compactIntegralSmulRingHom j p) n (p ^ e) x, Nat.cast_pow]

private lemma pow_smul_eq_nsmul_compactFinite (m n e : ℕ) (y : CompactFiniteAdicH j p m n) :
    (p : ℤ_[p]) ^ e • y = (p ^ e) • y := by
  rw [← Ext.smul_natCast_eq_nsmul (compactFiniteSmulRingHom j p m) n (p ^ e) y, Nat.cast_pow]

/-- **Bockstein, second part.** If `pᵉ` kills the `p`-power torsion of `Hⁿ⁺¹(T, j_! ℤ_p)`,
then the image of `ρₘ : Hⁿ(T, j_! ℤ_p) ⟶ Hⁿ(T, j_! ℤ/pᵐ)` contains `pᵉ Hⁿ(T, j_! ℤ/pᵐ)`. -/
theorem pow_smul_mem_range_compactReduction (m n e : ℕ)
    (he : ∀ x : CompactIntegralAdicH j p (n + 1), (∃ k, (p : ℤ_[p]) ^ k • x = 0) →
      (p : ℤ_[p]) ^ e • x = 0)
    (y : CompactFiniteAdicH j p m n) :
    (p : ℤ_[p]) ^ e • y ∈ LinearMap.range (compactReduction j p m n) := by
  have hδ (k : ℕ) : compactBocksteinδ j p m n ((p : ℤ_[p]) ^ k • y) =
      (p : ℤ_[p]) ^ k • compactBocksteinδ j p m n y := by
    rw [pow_smul_eq_nsmul_compactFinite, pow_smul_eq_nsmul_compactIntegral, map_nsmul]
  have h0 : compactBocksteinδ j p m n ((p : ℤ_[p]) ^ e • y) = 0 := by
    rw [hδ, he _ ⟨m, by rw [← hδ, pow_smul_compactFiniteAdicH, map_zero]⟩]
  obtain ⟨x, hx⟩ := Ext.covariant_sequence_exact₃ _
    (shortExact_compactBocksteinShortComplex j p m) ((p : ℤ_[p]) ^ e • y) rfl h0
  exact ⟨x, hx⟩


section Separation

variable {j p}

/-- The tower `j_! C(-, ℤ_p / pᵐ)` of extensions by zero. -/
noncomputable abbrev compactContinuousSheafTower :
    ℕᵒᵖ ⥤ Sheaf (Scheme.ProEt.topology T) AddCommGrpCat.{u + 1} :=
  continuousSheafTower U (powOpenAddSubgroup p) (powOpenAddSubgroup_succ_le p) ⋙
    (j)_!open[AddCommGrpCat.{u + 1}]

variable (j p) in
/-- The cone `j_! C(-, ℤ_p) ⟶ j_! C(-, ℤ_p / pᵐ)` over the tower `compactContinuousSheafTower`. -/
noncomputable abbrev compactContinuousSheafCone :
    Cone (compactContinuousSheafTower (j := j) (p := p)) :=
  (j)_!open[AddCommGrpCat.{u + 1}].mapCone
    (continuousSheafCone U (powOpenAddSubgroup p) (powOpenAddSubgroup_succ_le p))

/-- **Separation in degree `n + 1`**, given that `j_! C(-, ℤ_p)` is the limit of the tower
`j_! C(-, ℤ/pᵐ)`. -/
theorem eq_zero_of_forall_compactReduction_eq_zero_succ_of_isLimit
    (hlim : IsLimit (compactContinuousSheafCone j p)) (n : ℕ)
    (hfin : ∀ m, Finite (CompactFiniteAdicH j p m n)) (x : CompactIntegralAdicH j p (n + 1))
    (hx : ∀ m, compactReduction j p m (n + 1) x = 0) : x = 0 := by
  have hU := powOpenAddSubgroup_succ_le p
  have hrep := Scheme.ProEt.epiπAppZeroOfEpi_addCommGrpCat (S := T)
  have := Abelian.hasFiniteBiproducts (C := Sheaf (Scheme.ProEt.topology T) AddCommGrpCat.{u + 1})
  have := lim_preservesEpimorphisms_of_epi_π_app_zero hrep
  have := hasExactLimitsOfShape_of_preservesEpi
    (Sheaf (Scheme.ProEt.topology T) AddCommGrpCat.{u + 1}) (Discrete ℕ)
  have hepi (k : ℕ) :
      Epi ((compactContinuousSheafTower (j := j) (p := p)).map (homOfLE k.le_succ).op) := by
    rw [Functor.comp_map, continuousSheafTower_map_succ]
    have : Epi (continuousSheafMap U (openAddSubgroupQuotientMap (powOpenAddSubgroup p) hU k)) :=
      (shortExact_continuousSheafShortComplex U (powOpenAddSubgroup p) hU k).epi_g
    exact (j)_!open[AddCommGrpCat.{u + 1}].map_epi _
  refine Ext.eq_zero_of_isLimit_tower _
    (fun P hP t ht ↦ epi_one_sub_of_epiπAppZeroOfEpi hrep hepi hP t ht) hlim (q := n)
    (fun y ↦ ?_) x hx
  let F := compactContinuousSheafTower (j := j) (p := p)
  have (k : ℕ) : Finite (Sheaf.H (F.obj (op k)) n) := hfin k
  obtain ⟨w, hw⟩ := AddCommGroup.exists_sub_map_succ_eq_of_finite
    (G := fun k ↦ Sheaf.H (F.obj (op k)) n)
    (fun k ↦ (Ext.mk₀ (F.map (homOfLE k.le_succ).op)).postcomp _ (add_zero n)) y
  exact ⟨w, hw⟩

/-- **Separation in degree `0`**, given that `j_! C(-, ℤ_p)` is the limit of the tower
`j_! C(-, ℤ/pᵐ)`. -/
theorem eq_zero_of_forall_compactReduction_eq_zero_zero_of_isLimit
    (hlim : IsLimit (compactContinuousSheafCone j p)) (x : CompactIntegralAdicH j p 0)
    (hx : ∀ m, compactReduction j p m 0 x = 0) : x = 0 := by
  obtain ⟨f, rfl⟩ := (Ext.mk₀_bijective _ _).2 x
  have hf : f = 0 := by
    refine hlim.hom_ext fun ⟨m⟩ ↦ ?_
    rw [zero_comp]
    refine (Ext.mk₀_bijective _ _).1 ?_
    rw [Ext.mk₀_zero, ← Ext.mk₀_comp_mk₀]
    exact hx m
  rw [hf, Ext.mk₀_zero]

/-- **Separation**, given that `j_! C(-, ℤ_p)` is the limit of the tower `j_! C(-, ℤ/pᵐ)`: if
the groups `Hⁿ⁻¹(T, j_! ℤ/pᵐ)` are finite, a class of `Hⁿ(T, j_! ℤ_p)` whose reductions modulo
all `pᵐ` vanish is zero. -/
theorem eq_zero_of_forall_compactReduction_eq_zero_of_isLimit
    (hlim : IsLimit (compactContinuousSheafCone j p)) (n : ℕ)
    (hfin : ∀ m k, k + 1 = n → Finite (CompactFiniteAdicH j p m k))
    (x : CompactIntegralAdicH j p n) (hx : ∀ m, compactReduction j p m n x = 0) : x = 0 := by
  cases n with
  | zero => exact eq_zero_of_forall_compactReduction_eq_zero_zero_of_isLimit hlim x hx
  | succ n =>
    exact eq_zero_of_forall_compactReduction_eq_zero_succ_of_isLimit hlim n
      (fun m ↦ hfin m n rfl) x hx

/-- **Finite generation**, given that `j_! C(-, ℤ_p)` is the limit of the tower
`j_! C(-, ℤ/pᵐ)`: if the groups `Hⁿ⁻¹(T, j_! ℤ/pᵐ)` and `Hⁿ(T, j_! ℤ/p)` are finite, then
`Hⁿ(T, j_! ℤ_p)` is a finitely generated `ℤ_p`-module. -/
theorem module_finite_compactIntegralAdicH_of_isLimit
    (hlim : IsLimit (compactContinuousSheafCone j p)) (n : ℕ)
    (hfin : ∀ m k, k + 1 = n → Finite (CompactFiniteAdicH j p m k))
    [Finite (CompactFiniteAdicH j p 1 n)] :
    Module.Finite ℤ_[p] (CompactIntegralAdicH j p n) :=
  PadicInt.module_finite_of_finite_quotient (fun m ↦ compactReduction j p m n)
    (fun m y ↦ pow_smul_compactFiniteAdicH j p m n y)
    (fun m _ ha ↦ exists_eq_pow_smul_of_compactReduction_eq_zero j p m n ha)
    (fun a ha ↦ eq_zero_of_forall_compactReduction_eq_zero_of_isLimit hlim n hfin a ha)

variable [QuasiCompact j]

variable (j p) in
/-- **`j_! C(-, ℤ_p)` is the limit of the `j_! C(-, ℤ/pᵐ)`**, for a quasi-compact open immersion
`j`: the extension by zero preserves sequential limits
(`AlgebraicGeometry.ProEtale.isLimitMapConeOpenImmersionLowerShriek`). -/
noncomputable def isLimitCompactContinuousSheafCone :
    IsLimit (compactContinuousSheafCone j p) :=
  isLimitMapConeOpenImmersionLowerShriek
    (isLimitContinuousSheafCone U (powOpenAddSubgroup p) (powOpenAddSubgroup_succ_le p)
      (eq_zero_of_forall_mem_powOpenAddSubgroup p))

variable (j p) in
/-- **Separation.** For a quasi-compact open immersion `j : U ⟶ T`, if the groups
`Hⁿ⁻¹(T, j_! ℤ/pᵐ)` are finite (no condition for `n = 0`), a class of `Hⁿ(T, j_! ℤ_p)` whose
reductions modulo all `pᵐ` vanish is zero. -/
theorem eq_zero_of_forall_compactReduction_eq_zero (n : ℕ)
    (hfin : ∀ m k, k + 1 = n → Finite (CompactFiniteAdicH j p m k))
    (x : CompactIntegralAdicH j p n) (hx : ∀ m, compactReduction j p m n x = 0) : x = 0 :=
  eq_zero_of_forall_compactReduction_eq_zero_of_isLimit
    (isLimitCompactContinuousSheafCone j p) n hfin x hx

variable (j p) in
/-- **Finite generation of compactly supported `ℓ`-adic cohomology.** For a quasi-compact open
immersion `j : U ⟶ T`, if the groups `Hⁿ⁻¹(T, j_! ℤ/pᵐ)` and `Hⁿ(T, j_! ℤ/p)` are finite, then
`Hⁿ(T, j_! ℤ_p)` is a finitely generated `ℤ_p`-module. -/
theorem module_finite_compactIntegralAdicH (n : ℕ)
    (hfin : ∀ m k, k + 1 = n → Finite (CompactFiniteAdicH j p m k))
    [Finite (CompactFiniteAdicH j p 1 n)] :
    Module.Finite ℤ_[p] (CompactIntegralAdicH j p n) :=
  module_finite_compactIntegralAdicH_of_isLimit (isLimitCompactContinuousSheafCone j p) n hfin

/-- **Compatible lifts.** For a quasi-compact open immersion `j`, a family of classes
`zₘ ∈ Hⁿ(T, j_! ℤ/pᵐ)` compatible under the transition maps is the family of reductions of a
class of `Hⁿ(T, j_! ℤ_p)`. -/
theorem exists_compactReduction_eq {n : ℕ} (z : ∀ m, CompactFiniteAdicH j p m n)
    (hz : ∀ m, Ext.comp (C := Sheaf (Scheme.ProEt.topology T) AddCommGrpCat.{u + 1}) (z (m + 1))
      (Ext.mk₀ ((compactContinuousSheafTower (j := j) (p := p)).map (homOfLE m.le_succ).op))
        (add_zero n) = z m) :
    ∃ x : CompactIntegralAdicH j p n, ∀ m, compactReduction j p m n x = z m := by
  have hU := powOpenAddSubgroup_succ_le p
  have hrep := Scheme.ProEt.epiπAppZeroOfEpi_addCommGrpCat (S := T)
  have := Abelian.hasFiniteBiproducts (C := Sheaf (Scheme.ProEt.topology T) AddCommGrpCat.{u + 1})
  have := lim_preservesEpimorphisms_of_epi_π_app_zero hrep
  have := hasExactLimitsOfShape_of_preservesEpi
    (Sheaf (Scheme.ProEt.topology T) AddCommGrpCat.{u + 1}) (Discrete ℕ)
  have hepi (k : ℕ) :
      Epi ((compactContinuousSheafTower (j := j) (p := p)).map (homOfLE k.le_succ).op) := by
    rw [Functor.comp_map, continuousSheafTower_map_succ]
    have : Epi (continuousSheafMap U (openAddSubgroupQuotientMap (powOpenAddSubgroup p) hU k)) :=
      (shortExact_continuousSheafShortComplex U (powOpenAddSubgroup p) hU k).epi_g
    exact (j)_!open[AddCommGrpCat.{u + 1}].map_epi _
  obtain ⟨x, hx⟩ := Ext.exists_comp_eq_of_isLimit_tower _
    (fun P hP t ht ↦ epi_one_sub_of_epiπAppZeroOfEpi hrep hepi hP t ht)
    (isLimitCompactContinuousSheafCone j p) (q := n) z hz
  exact ⟨x, hx⟩

end Separation

end AlgebraicGeometry.ProEtale
