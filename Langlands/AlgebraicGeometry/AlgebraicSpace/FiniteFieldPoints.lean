import Langlands.AlgebraicGeometry.AlgebraicSpace.EtaleChartFibreCount
import Langlands.Global.AdelicSpaceLevelPointsStatement
import Mathlib.FieldTheory.Finite.GaloisField

/-!
# Finitely many points over a finite field

Let `X` be a quasi-separated algebraic space of finite type over `Spec C`, and `κ` a finite
field with a `C`-algebra structure. Then `X(κ)` is finite.

Cover a quasi-compact atlas of `X` by finitely many affine opens `V`. A `κ`-point `x` of `X`
has a point in the fibre of the atlas with values in a finite separable extension `L` of
`κ` (`FieldPointEtaleLift.exists_separable_point_mono`), lying on some `V`. Its twists by
`Gal(L/κ)` are `[L : κ]` distinct `L`-points of `V` with the same image in `X`, so
`[L : κ]` is bounded by the fibre bound of `EtaleChartFibreCount.exists_fibre_card_le`.
All such `L` embed into one finite extension `M` of `κ`. So `x` becomes, over `M`, the image
of one of the finitely many `M`-points of the charts, and `X(κ) → X(M)` is injective.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite Polynomial
open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology (ringTest RingPoint ringTestMap ringTestMap_comp
  ringTestMap_id ringTestMap_left AffineCoordinateRing affineSchemePointEquiv AlgPoint)

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

namespace FiniteFieldPoints

open FieldPointEtaleLift

/-- A finite field has a finite extension into which every extension of degree at most `D`
embeds: the splitting field of `X ^ (q ^ D!) - X`. -/
theorem exists_extension_embedding (κ : Type u) [Field κ] [Finite κ] (D : ℕ) :
    ∃ (M : Type u) (_ : Field M) (_ : Algebra κ M), FiniteDimensional κ M ∧
      ∀ (L : Type u) [Field L] [Algebra κ L] [FiniteDimensional κ L],
        Module.finrank κ L ≤ D → Nonempty (L →ₐ[κ] M) := by
  classical
  have := Fintype.ofFinite κ
  let f : κ[X] := X ^ Fintype.card κ ^ D.factorial - X
  have hf : f ≠ 0 := FiniteField.X_pow_card_pow_sub_X_ne_zero κ (Nat.factorial_ne_zero D)
    Fintype.one_lt_card
  refine ⟨f.SplittingField, inferInstance, inferInstance, inferInstance,
    fun L _ _ _ hL => ?_⟩
  have := Module.finite_of_finite κ (M := L)
  have := Fintype.ofFinite L
  have hd : Module.finrank κ L ∣ D.factorial :=
    Nat.dvd_factorial Module.finrank_pos hL
  refine ⟨Polynomial.IsSplittingField.lift _ (X ^ Fintype.card L - X) ?_⟩
  refine (SplittingField.splits f).of_dvd (map_ne_zero hf) ?_
  rw [Module.card_eq_pow_finrank (K := κ) (V := L)]
  exact (map_dvd_map' _).mpr (dvd_pow_pow_sub_self_of_dvd hd)

variable {C : Type u} [CommRing C]

/-- An affine scheme locally of finite type over `C` has finitely many points with values in
a finite `C`-algebra. -/
theorem finite_ringPoint {V : Over (Spec (CommRingCat.of C))} [IsAffine V.left]
    [LocallyOfFiniteType V.hom] (M : Type u) [CommRing M] [Algebra C M] [Finite M] :
    Finite (RingPoint C V M) := by
  classical
  obtain ⟨s, hs⟩ := (inferInstance : Algebra.FiniteType C (AffineCoordinateRing C V)).out
  have hinj : Function.Injective fun φ : AffineCoordinateRing C V →ₐ[C] M => fun a : s => φ a :=
    fun φ ψ h => AlgHom.ext_of_adjoin_eq_top hs fun a ha => congrFun h ⟨a, ha⟩
  have : Finite (AffineCoordinateRing C V →ₐ[C] M) := Finite.of_injective _ hinj
  exact Finite.of_equiv _ ((affineSchemePointEquiv C V M).trans AlgPoint.algHomEquiv).symm

/-- **Points over a finite field are finite in number.** -/
theorem finite_ringPoints (X : AlgebraicSpace (Spec (CommRingCat.of C))) (hX : IsQuasiSeparated X)
    (hft : FiniteTypeOverRing C X) (κ : Type u) [Field κ] [Finite κ] [Algebra C κ] :
    Finite (RingPoints C X κ) := by
  classical
  obtain ⟨U, a, ha, hs, hU⟩ := hft.exists_atlas
  have : LocallyOfFiniteType U.hom := hU.1
  have : QuasiCompact U.hom := hU.2
  have : CompactSpace U.left := QuasiCompact.compactSpace_of_compactSpace U.hom
  obtain ⟨t, ht⟩ : ∃ t : Finset U.left.affineOpens,
      ∀ x : U.left, ∃ W ∈ t, x ∈ (W : U.left.Opens) := by
    obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
      (fun W : U.left.affineOpens => ((W : U.left.Opens) : Set U.left))
      (fun W => W.1.isOpen) (fun x _ => by
        obtain ⟨W, hW, hx, -⟩ := exists_isAffineOpen_mem_and_subset
          (show x ∈ (⊤ : U.left.Opens) from trivial)
        exact Set.mem_iUnion.2 ⟨⟨W, hW⟩, hx⟩)
    refine ⟨t, fun x => ?_⟩
    have hx := ht (Set.mem_univ x)
    simp only [Set.mem_iUnion] at hx
    obtain ⟨W, hW, hx⟩ := hx
    exact ⟨W, hW, hx⟩
  -- the affine charts
  let V : U.left.affineOpens → Over (Spec (CommRingCat.of C)) := fun W => OverAction.resOver W.1
  let aW : ∀ W, (schemeYoneda _).obj (V W) ⟶ X.presheaf := fun W =>
    (schemeYoneda _).map (OverAction.resOverι W.1) ≫ a
  have haW : ∀ W, IsEtale (aW W) := fun W =>
    IsEtale.comp (isEtale_map _ (inferInstanceAs (Etale W.1.ι))) ha
  have hVaff : ∀ W, IsAffine (V W).left := fun W => W.2
  have hVlft : ∀ W, LocallyOfFiniteType (V W).hom := fun W => by
    change LocallyOfFiniteType (W.1.ι ≫ U.hom)
    infer_instance
  choose D hD using fun W => @EtaleChartFibreCount.exists_fibre_card_le _ _ _ _ (aW W) hX (haW W)
    (hVaff W)
  obtain ⟨M, _, _, hM, hMemb⟩ := exists_extension_embedding κ (∑ W ∈ t, D W)
  have : Finite M := Module.finite_of_finite κ
  let _ : Algebra C M := ((algebraMap κ M).comp (algebraMap C κ)).toAlgebra
  have : IsScalarTower C κ M := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hfin : ∀ W, Finite (RingPoint C (V W) M) := fun W => by
    have := hVaff W
    have := hVlft W
    exact finite_ringPoint M
  -- every `κ`-point becomes, over `M`, the image of an `M`-point of a chart in `t`
  have hmem : ∀ x : RingPoints C X κ, ∃ W ∈ t, ∃ v : RingPoint C (V W) M,
      RingPoints.map (AlgebraicSpace.homMk (aW W)) ((schemeRingPointsEquiv C (V W) M).symm v) =
        RingPoints.changeRing (IsScalarTower.toAlgHom C κ M) x := by
    intro x
    let xh : (schemeYoneda (Spec (CommRingCat.of C))).obj (ringTest C κ) ⟶ X.presheaf :=
      uliftYonedaEquiv.symm x
    let hr := X.representable_from_scheme a
    let P := hr.pullback xh
    let p : P ⟶ ringTest C κ := hr.snd xh
    let q : P ⟶ U := Functor.relativelyRepresentable.fst' hr xh
    have hsq : IsPullback ((schemeYoneda _).map q) ((schemeYoneda _).map p) a xh :=
      Functor.relativelyRepresentable.isPullback' hr xh
    have hpe : Etale p.left := ha.projection xh _ p hsq
    have hps : Surjective p.left := hs.projection xh _ p hsq
    let T : Over (Spec (CommRingCat.of κ)) := Over.mk p.left
    have : Etale T.hom := hpe
    have : Nonempty T.left := by
      obtain ⟨y⟩ : Nonempty (Spec (CommRingCat.of κ)) := inferInstance
      obtain ⟨z, -⟩ := hps.surj y
      exact ⟨z⟩
    obtain ⟨L, _, _, hL, hLs, w₀, hw₀⟩ := exists_separable_point_mono T
    have := hL
    have : Finite L := Module.finite_of_finite κ
    let _ : Algebra C L := ((algebraMap κ L).comp (algebraMap C κ)).toAlgebra
    have : IsScalarTower C κ L := IsScalarTower.of_algebraMap_eq fun _ => rfl
    let w₀l : (ringTest C L).left ⟶ P.left := w₀.left
    have hw₀p : w₀l ≫ p.left = (fieldTestMap (C := C) (k := κ) (K := L)).left := Over.w w₀
    have : Mono w₀l := hw₀
    let w₁ : ringTest C L ⟶ P := Over.homMk w₀l (by
      rw [← Over.w p, ← Category.assoc, hw₀p]
      exact Over.w (fieldTestMap (C := C) (k := κ) (K := L)))
    have hw₁p : w₁ ≫ p = fieldTestMap (C := C) (k := κ) (K := L) := Over.OverMorphism.ext hw₀p
    -- the chart containing the point
    let v₁ : ringTest C L ⟶ U := w₁ ≫ q
    obtain ⟨y₀⟩ : Nonempty (Spec (CommRingCat.of L)) := inferInstance
    obtain ⟨W, hWt, hyW⟩ := ht (v₁.left y₀)
    have hrange : Set.range v₁.left ⊆ Set.range (OverAction.resOverι W.1).left := by
      rintro _ ⟨y', rfl⟩
      rw [Subsingleton.elim y' y₀]
      exact ⟨⟨v₁.left y₀, hyW⟩, Scheme.Opens.ι_apply _ _⟩
    obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : ringTest C L ⟶ V W, ℓ ≫ OverAction.resOverι W.1 = v₁ := by
      let ℓ' := _root_.AlgebraicGeometry.IsOpenImmersion.lift (OverAction.resOverι W.1).left
        v₁.left hrange
      have hℓ' : ℓ' ≫ (OverAction.resOverι W.1).left = v₁.left :=
        _root_.AlgebraicGeometry.IsOpenImmersion.lift_fac _ _ hrange
      refine ⟨Over.homMk ℓ' ?_, Over.OverMorphism.ext hℓ'⟩
      change ℓ' ≫ (OverAction.resOverι W.1).left ≫ U.hom = (ringTest C L).hom
      rw [reassoc_of% hℓ', Over.w v₁]
    -- the Galois twists of the point
    let vσ : (L ≃ₐ[κ] L) → (ringTest C L ⟶ V W) := fun σ =>
      ringTestMap C ((σ : L →ₐ[κ] L).restrictScalars C) ≫ ℓ
    have hwp : ∀ σ : L ≃ₐ[κ] L,
        (ringTestMap C ((σ : L →ₐ[κ] L).restrictScalars C) ≫ w₁) ≫ p =
          fieldTestMap (C := C) (k := κ) (K := L) := by
      intro σ
      rw [Category.assoc, hw₁p, ← ringTestMap_comp]
      congr 1
      ext c
      exact σ.commutes c
    have hvE : ∀ σ, (schemeYoneda _).map (vσ σ) ≫ aW W =
        (schemeYoneda _).map (fieldTestMap (C := C) (k := κ) (K := L)) ≫ xh := fun σ => by
      change (schemeYoneda _).map (vσ σ) ≫ (schemeYoneda _).map (OverAction.resOverι W.1) ≫ a = _
      rw [← Functor.map_comp_assoc]
      have hvι : vσ σ ≫ OverAction.resOverι W.1 =
          (ringTestMap C ((σ : L →ₐ[κ] L).restrictScalars C) ≫ w₁) ≫ q := by
        change (ringTestMap C _ ≫ ℓ) ≫ _ = _
        rw [Category.assoc, hℓ, Category.assoc]
      rw [hvι, Functor.map_comp_assoc, hsq.w, ← Functor.map_comp_assoc, hwp]
    have hvinj : Function.Injective vσ := by
      intro σ τ hστ
      have hq : (ringTestMap C ((σ : L →ₐ[κ] L).restrictScalars C) ≫ w₁) ≫ q =
          (ringTestMap C ((τ : L →ₐ[κ] L).restrictScalars C) ≫ w₁) ≫ q := by
        have h1 : vσ σ ≫ OverAction.resOverι W.1 = vσ τ ≫ OverAction.resOverι W.1 := by
          rw [hστ]
        change (ringTestMap C _ ≫ ℓ) ≫ _ = (ringTestMap C _ ≫ ℓ) ≫ _ at h1
        simp only [Category.assoc, hℓ] at h1
        simpa only [Category.assoc] using h1
      have hw : ringTestMap C ((σ : L →ₐ[κ] L).restrictScalars C) ≫ w₁ =
          ringTestMap C ((τ : L →ₐ[κ] L).restrictScalars C) ≫ w₁ :=
        Functor.relativelyRepresentable.hom_ext' hr hq (by rw [hwp, hwp])
      have h1 : (ringTestMap C ((σ : L →ₐ[κ] L).restrictScalars C)).left ≫ w₀l =
          (ringTestMap C ((τ : L →ₐ[κ] L).restrictScalars C)).left ≫ w₀l :=
        congrArg CommaMorphism.left hw
      rw [cancel_mono, ringTestMap_left, ringTestMap_left] at h1
      have h2 := Spec.map_injective h1
      ext z
      exact congrArg (fun φ => φ.hom z) h2
    -- the degree bound
    have hℓa : (schemeYoneda _).map ℓ ≫ aW W =
        (schemeYoneda _).map (fieldTestMap (C := C) (k := κ) (K := L)) ≫ xh := by
      have h := hvE 1
      have h1 : vσ 1 = ℓ := by
        change ringTestMap C _ ≫ ℓ = ℓ
        rw [show ((1 : L ≃ₐ[κ] L) : L →ₐ[κ] L).restrictScalars C = AlgHom.id C L from
          AlgHom.ext fun _ => rfl, ringTestMap_id, Category.id_comp]
      rwa [h1] at h
    have hcard : Fintype.card (L ≃ₐ[κ] L) ≤ D W :=
      hD W L ℓ (L ≃ₐ[κ] L) vσ hvinj fun σ => (hvE σ).trans hℓa.symm
    have hdeg : Module.finrank κ L ≤ ∑ W ∈ t, D W := by
      rw [← IsGalois.card_aut_eq_finrank, ← Fintype.card_eq_nat_card]
      exact hcard.trans (Finset.single_le_sum (fun _ _ => Nat.zero_le _) hWt)
    obtain ⟨e⟩ := hMemb L hdeg
    -- the point over `M`
    let v : ringTest C M ⟶ V W := ringTestMap C (e.restrictScalars C) ≫ ℓ
    refine ⟨W, hWt, v, ?_⟩
    have e₁ : RingPoints.map (AlgebraicSpace.homMk (aW W))
        ((schemeRingPointsEquiv C (V W) M).symm v) =
          uliftYonedaEquiv.{u + 1} ((schemeYoneda _).map v ≫ aW W) := by
      rw [uliftYonedaEquiv_comp, uliftYonedaEquiv_uliftYoneda_map]
      rfl
    have hvM : (schemeYoneda _).map v ≫ aW W =
        (schemeYoneda _).map (fieldTestMap (C := C) (k := κ) (K := M)) ≫ xh := by
      change (schemeYoneda _).map (ringTestMap C (e.restrictScalars C) ≫ ℓ) ≫ aW W = _
      rw [Functor.map_comp_assoc, hℓa, ← Functor.map_comp_assoc, ← ringTestMap_comp]
      congr 3
      ext c
      exact e.commutes c
    have e₂ : x = uliftYonedaEquiv xh := (Equiv.apply_symm_apply _ _).symm
    rw [e₁, hvM]
    change _ = X.presheaf.map (fieldTestMap (C := C) (k := κ) (K := M)).op x
    rw [e₂, uliftYonedaEquiv_naturality]
    rfl
  -- conclude
  let S : Set (RingPoints C X M) := ⋃ W ∈ t, Set.range fun v : RingPoint C (V W) M =>
    RingPoints.map (AlgebraicSpace.homMk (aW W)) ((schemeRingPointsEquiv C (V W) M).symm v)
  have hS : S.Finite := Set.Finite.biUnion t.finite_toSet fun W _ => by
    have := hfin W
    exact Set.finite_range _
  have := hS.to_subtype
  have hxS : ∀ x : RingPoints C X κ, RingPoints.changeRing (IsScalarTower.toAlgHom C κ M) x ∈ S := by
    intro x
    obtain ⟨W, hWt, v, hv⟩ := hmem x
    exact Set.mem_biUnion hWt ⟨v, hv⟩
  exact Finite.of_injective (fun x => (⟨_, hxS x⟩ : S))
    fun x y hxy => changeRing_injective (K := M) X (congrArg Subtype.val hxy)

end FiniteFieldPoints

end Langlands.AlgebraicGeometry.AlgebraicSpace
