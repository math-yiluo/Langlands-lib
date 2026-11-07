import Langlands.AlgebraicGeometry.AlgebraicSpace.EtaleChartFibreCount
import Langlands.AlgebraicGeometry.AlgebraicSpace.UnramifiedHenselExtension
import Langlands.AlgebraicGeometry.AlgebraicSpace.HenselianIntegralPointsOpenProof
import Langlands.CommutativeAlgebra.HenselianSections
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra

/-!
# Lifting points of an algebraic space to an étale chart over a finite free extension

Let `X` be a quasi-separated algebraic space over `Spec C` with an étale surjective chart
`a : h_U → X` from an affine scheme. For a complete local `C`-algebra `O` and `x ∈ X(O)`, there is
a finite free henselian extension `O → O_e = O[X]/(m)` of rank at most a bound `D` depending on the
chart, and an `O_e`-point of `U` mapping to the image of `x`. This is the local step of Conrad's
proof of Proposition 5.2.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite Polynomial Module IntermediateField
open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology (RingPoint ringTest ringTestMap ringTestMap_comp
  ringTestMap_left)

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

namespace ProductPointsLocalLift

section Hensel

variable {C : Type u} [CommRing C] {X : AlgebraicSpace (Spec (CommRingCat.of C))}
  {U : Over (Spec (CommRingCat.of C))} (a : (schemeYoneda _).obj U ⟶ X.presheaf)

/-- **Lifting along an étale chart over a henselian local ring.** Let `O` be a henselian local
`C`-algebra and `O → K` a surjection onto a field. If `x ∈ X(O)` and a `K`-point of `U` maps to
the image of `x` in `X(K)`, then `x` is the image of an `O`-point of `U`. -/
theorem exists_point_of_field_point (ha : IsEtale a) {O K : Type u} [CommRing O]
    [HenselianLocalRing O] [Field K] [Algebra C O] [Algebra O K] [Algebra C K]
    [IsScalarTower C O K] (hK : Function.Surjective (algebraMap O K))
    (x : RingPoints C X O) (ū : ringTest C K ⟶ U)
    (hū : (schemeYoneda _).map ū ≫ a =
      (schemeYoneda _).map (ringTestMap C (IsScalarTower.toAlgHom C O K)) ≫
        uliftYonedaEquiv.symm x) :
    ∃ u : ringTest C O ⟶ U, (schemeYoneda _).map u ≫ a = uliftYonedaEquiv.symm x := by
  let hr := X.representable_from_scheme a
  let xh : (schemeYoneda (Spec (CommRingCat.of C))).obj (ringTest C O) ⟶ X.presheaf :=
    uliftYonedaEquiv.symm x
  let P := hr.pullback xh
  let p : P ⟶ ringTest C O := hr.snd xh
  let q : P ⟶ U := Functor.relativelyRepresentable.fst' hr xh
  have hsq : IsPullback ((schemeYoneda _).map q) ((schemeYoneda _).map p) a xh :=
    Functor.relativelyRepresentable.isPullback' hr xh
  let pl : P.left ⟶ Spec (CommRingCat.of O) := p.left
  have : Etale pl := ha.projection xh _ p hsq
  let π : ringTest C K ⟶ ringTest C O := ringTestMap C (IsScalarTower.toAlgHom C O K)
  let b : ringTest C K ⟶ P := Functor.relativelyRepresentable.lift' hr ū π hū
  have hbp : b ≫ p = π := Functor.relativelyRepresentable.lift'_snd hr ū π hū
  have hb : b.left ≫ pl = Spec.map (CommRingCat.ofHom (algebraMap O K)) := by
    change (b ≫ p).left = _
    rw [hbp, ringTestMap_left]
    rfl
  obtain ⟨σ, hσ, -⟩ :=
    CommutativeAlgebra.HenselianSections.exists_section_of_smooth_of_surjective hK pl b.left hb
  let σ' : ringTest C O ⟶ P := Over.homMk σ (by
    change σ ≫ P.hom = (ringTest C O).hom
    rw [← Over.w p]
    let rh : Spec (CommRingCat.of O) ⟶ Spec (CommRingCat.of C) := (ringTest C O).hom
    change σ ≫ pl ≫ rh = rh
    rw [← Category.assoc, hσ, Category.id_comp])
  have hσp : σ' ≫ p = 𝟙 _ := Over.OverMorphism.ext (by
    change σ ≫ pl = 𝟙 _
    exact hσ)
  refine ⟨σ' ≫ q, ?_⟩
  rw [Functor.map_comp_assoc, hsq.w, ← Functor.map_comp_assoc, hσp,
    CategoryTheory.Functor.map_id, Category.id_comp]

end Hensel

section Fibre

variable {C : Type u} [CommRing C] {X : AlgebraicSpace (Spec (CommRingCat.of C))}
  {U : Over (Spec (CommRingCat.of C))} (a : (schemeYoneda _).obj U ⟶ X.presheaf)

open FieldPointEtaleLift in
/-- **Fibre points of bounded degree.** For an étale surjective chart `a : h_U → X` of a
quasi-separated space from an affine scheme, there is a bound `D` such that every field-valued
point `xr ∈ X(κ)` lifts to `U` over a finite separable extension of `κ` of degree at most `D`. -/
theorem exists_fibre_point (hX : IsQuasiSeparated X) (ha : IsEtale a) (hs : IsSurjective a)
    [IsAffine U.left] :
    ∃ D : ℕ, ∀ (κ : Type u) [Field κ] [Algebra C κ] (xr : RingPoints C X κ),
      ∃ (L : Type u) (_ : Field L) (_ : Algebra κ L) (_ : Algebra C L) (_ : IsScalarTower C κ L),
        FiniteDimensional κ L ∧ Algebra.IsSeparable κ L ∧ Module.finrank κ L ≤ D ∧
        ∃ ū : ringTest C L ⟶ U, (schemeYoneda _).map ū ≫ a =
          (schemeYoneda _).map (ringTestMap C (IsScalarTower.toAlgHom C κ L)) ≫
            uliftYonedaEquiv.symm xr := by
  obtain ⟨D, hD⟩ := EtaleChartFibreCount.exists_fibre_card_le a hX ha
  refine ⟨D, fun κ _ _ xr => ?_⟩
  let xh : (schemeYoneda (Spec (CommRingCat.of C))).obj (ringTest C κ) ⟶ X.presheaf :=
    uliftYonedaEquiv.symm xr
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
  let _ : Algebra C L := ((algebraMap κ L).comp (algebraMap C κ)).toAlgebra
  have : IsScalarTower C κ L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let w₀l : (ringTest C L).left ⟶ P.left := w₀.left
  have hw₀p : w₀l ≫ p.left = (fieldTestMap (C := C) (k := κ) (K := L)).left := Over.w w₀
  have : Mono w₀l := hw₀
  let w₁ : ringTest C L ⟶ P := Over.homMk w₀l (by
    rw [← Over.w p, ← Category.assoc, hw₀p]
    exact Over.w (fieldTestMap (C := C) (k := κ) (K := L)))
  have hw₁p : w₁ ≫ p = fieldTestMap (C := C) (k := κ) (K := L) := Over.OverMorphism.ext hw₀p
  let v₁ : ringTest C L ⟶ U := w₁ ≫ q
  have hv₁ : (schemeYoneda _).map v₁ ≫ a =
      (schemeYoneda _).map (fieldTestMap (C := C) (k := κ) (K := L)) ≫ xh := by
    rw [Functor.map_comp_assoc, hsq.w, ← Functor.map_comp_assoc, hw₁p]
  refine ⟨L, inferInstance, inferInstance, inferInstance, inferInstance, hL, hLs, ?_, v₁, hv₁⟩
  -- the degree bound, through the embeddings into an algebraic closure
  let Ω := AlgebraicClosure L
  let vσ : (L →ₐ[κ] Ω) → (ringTest C Ω ⟶ U) := fun σ =>
    ringTestMap C (σ.restrictScalars C) ≫ v₁
  have hwp : ∀ σ : L →ₐ[κ] Ω, (ringTestMap C (σ.restrictScalars C) ≫ w₁) ≫ p =
      fieldTestMap (C := C) (k := κ) (K := Ω) := by
    intro σ
    rw [Category.assoc, hw₁p, ← ringTestMap_comp]
    congr 1
    ext c
    exact σ.commutes c
  have hvE : ∀ σ, (schemeYoneda _).map (vσ σ) ≫ a =
      (schemeYoneda _).map (fieldTestMap (C := C) (k := κ) (K := Ω)) ≫ xh := fun σ => by
    change (schemeYoneda _).map ((ringTestMap C _ ≫ w₁) ≫ q) ≫ a = _
    rw [Functor.map_comp_assoc, hsq.w, ← Functor.map_comp_assoc, hwp]
  have hvinj : Function.Injective vσ := by
    intro σ τ hστ
    have hq : (ringTestMap C (σ.restrictScalars C) ≫ w₁) ≫ q =
        (ringTestMap C (τ.restrictScalars C) ≫ w₁) ≫ q := by
      simpa only [Category.assoc] using hστ
    have hw : ringTestMap C (σ.restrictScalars C) ≫ w₁ =
        ringTestMap C (τ.restrictScalars C) ≫ w₁ :=
      Functor.relativelyRepresentable.hom_ext' hr hq (by rw [hwp, hwp])
    have h1 : (ringTestMap C (σ.restrictScalars C)).left ≫ w₀l =
        (ringTestMap C (τ.restrictScalars C)).left ≫ w₀l :=
      congrArg CommaMorphism.left hw
    rw [cancel_mono, ringTestMap_left, ringTestMap_left] at h1
    have h2 := Spec.map_injective h1
    ext z
    exact congrArg (fun φ => φ.hom z) h2
  let σ₀ : L →ₐ[κ] Ω := IsScalarTower.toAlgHom κ L Ω
  let _ : Fintype (L →ₐ[κ] Ω) := Fintype.ofFinite _
  have hcard : Fintype.card (L →ₐ[κ] Ω) ≤ D :=
    hD Ω (vσ σ₀) (L →ₐ[κ] Ω) vσ hvinj fun σ => (hvE σ).trans (hvE σ₀).symm
  rw [Fintype.card_eq_nat_card,
    AlgHom.natCard_of_splits κ L Ω (fun _ => IsAlgClosed.splits _)] at hcard
  exact hcard

end Fibre

section Unramified

variable {O : Type u} [CommRing O] [IsLocalRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]

/-- **The unramified extension with a given residue field.** For a complete local ring `O` and a
finite separable extension `L` of its residue field, there is a henselian local `O`-algebra,
free of rank `[L : κ]` over `O`, with a surjection onto `L` compatible with `O → κ → L`. -/
theorem exists_unramified (L : Type u) [Field L] [Algebra (IsLocalRing.ResidueField O) L]
    [FiniteDimensional (IsLocalRing.ResidueField O) L]
    [Algebra.IsSeparable (IsLocalRing.ResidueField O) L] :
    ∃ (E : Type u) (_ : CommRing E) (_ : Algebra O E) (_ : HenselianLocalRing E)
      (_ : Basis (Fin (Module.finrank (IsLocalRing.ResidueField O) L)) O E) (ρ : E →+* L),
      Function.Surjective ρ ∧
        ρ.comp (algebraMap O E) =
          (algebraMap (IsLocalRing.ResidueField O) L).comp (IsLocalRing.residue O) := by
  let κ := IsLocalRing.ResidueField O
  obtain ⟨α, hα⟩ := Field.exists_primitive_element κ L
  have hint : IsIntegral κ α := Algebra.IsIntegral.isIntegral α
  have hres : Function.Surjective (IsLocalRing.residue O) := IsLocalRing.residue_surjective
  obtain ⟨m, hmap, hdeg, hmon⟩ := Polynomial.lifts_and_natDegree_eq_and_monic
    (Polynomial.map_surjective _ hres (minpoly κ α)) (minpoly.monic hint)
  have hirr : Fact (Irreducible (UnramifiedHensel.reduction m)) := ⟨by
    change Irreducible (m.map (IsLocalRing.residue O))
    rw [hmap]
    exact minpoly.irreducible hint⟩
  have hfr : (minpoly κ α).natDegree = Module.finrank κ L := by
    rw [← IntermediateField.adjoin.finrank hint, hα, IntermediateField.finrank_top']
  let := UnramifiedHensel.isLocalRing m hmon
  have hhen := UnramifiedHensel.henselianLocalRing m hmon
  let pb := AdjoinRoot.powerBasis' hmon
  have hdim : pb.dim = Module.finrank κ L := by
    rw [AdjoinRoot.powerBasis'_dim, hdeg, hfr]
  let b := pb.basis.reindex (finCongr hdim)
  have heval : (m.map ((algebraMap κ L).comp (IsLocalRing.residue O))).eval α = 0 := by
    rw [← Polynomial.map_map, hmap, Polynomial.eval_map, ← Polynomial.aeval_def, minpoly.aeval]
  let ρ : AdjoinRoot m →+* L := AdjoinRoot.lift ((algebraMap κ L).comp (IsLocalRing.residue O)) α
    (by rw [Polynomial.eval_map] at heval; exact heval)
  refine ⟨AdjoinRoot m, inferInstance, inferInstance, hhen, b, ρ, ?_, ?_⟩
  · intro y
    have hy : y ∈ (κ⟮α⟯ : IntermediateField κ L) := by rw [hα]; trivial
    rw [← IntermediateField.mem_toSubalgebra, IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic,
      Algebra.adjoin_singleton_eq_range_aeval] at hy
    obtain ⟨g, rfl⟩ := hy
    obtain ⟨g', rfl⟩ := Polynomial.map_surjective _ hres g
    refine ⟨AdjoinRoot.mk m g', ?_⟩
    rw [AdjoinRoot.lift_mk]
    change _ = Polynomial.aeval α (g'.map (IsLocalRing.residue O))
    rw [Polynomial.aeval_def, Polynomial.eval₂_map]
  · ext r
    simp [ρ]
    rfl

end Unramified

section Lift

variable {C : Type u} [CommRing C] {X : AlgebraicSpace (Spec (CommRingCat.of C))}
  {U : Over (Spec (CommRingCat.of C))} (a : (schemeYoneda _).obj U ⟶ X.presheaf)

/-- Change of coefficients on the Yoneda side. -/
theorem uliftYonedaEquiv_symm_changeRing {A B : Type u} [CommRing A] [CommRing B] [Algebra C A]
    [Algebra C B] (φ : A →ₐ[C] B) (x : RingPoints C X A) :
    uliftYonedaEquiv.{u + 1}.symm (RingPoints.changeRing φ x) =
      (schemeYoneda _).map (ringTestMap C φ) ≫ uliftYonedaEquiv.symm x :=
  uliftYonedaEquiv_symm_map (ringTestMap C φ).op x

/-- **The local lifting step of Proposition 5.2.** For an étale surjective chart `a : h_U → X`
of a quasi-separated space from an affine scheme, there is `d > 0` such that every point of `X`
with values in a complete local `C`-algebra `O` lifts to `U` over some finite free `O`-algebra of
rank `d`. -/
theorem exists_local_lift (hX : IsQuasiSeparated X) (ha : IsEtale a) (hs : IsSurjective a)
    [IsAffine U.left] :
    ∃ d : ℕ, 0 < d ∧ ∀ (O : Type u) [CommRing O] [IsLocalRing O]
      [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Algebra C O] (x : RingPoints C X O),
      ∃ (O' : Type u) (_ : CommRing O') (_ : Algebra O O') (_ : Algebra C O')
        (_ : IsScalarTower C O O') (_ : Basis (Fin d) O O') (u' : ringTest C O' ⟶ U),
        (schemeYoneda _).map u' ≫ a =
          (schemeYoneda _).map (ringTestMap C (IsScalarTower.toAlgHom C O O')) ≫
            uliftYonedaEquiv.symm x := by
  obtain ⟨D, hD⟩ := exists_fibre_point a hX ha hs
  refine ⟨D.factorial, Nat.factorial_pos D, fun O _ _ _ _ x => ?_⟩
  let κ := IsLocalRing.ResidueField O
  obtain ⟨L, _, _, _, _, hL, hLs, hdeg, ū, hū⟩ :=
    hD κ (RingPoints.changeRing (IsScalarTower.toAlgHom C O κ) x)
  obtain ⟨E, _, _, hE, b, ρ, hρs, hρ⟩ := exists_unramified (O := O) L
  let _ : Algebra C E := ((algebraMap O E).comp (algebraMap C O)).toAlgebra
  have : IsScalarTower C O E := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let _ : Algebra E L := ρ.toAlgebra
  have hρc : ∀ r : O, algebraMap E L (algebraMap O E r) =
      algebraMap κ L (IsLocalRing.residue O r) := fun r => congrArg (fun f => f r) hρ
  have : IsScalarTower C E L := IsScalarTower.of_algebraMap_eq fun c => by
    change algebraMap C L c = algebraMap E L (algebraMap O E (algebraMap C O c))
    rw [hρc, IsScalarTower.algebraMap_apply C κ L, IsScalarTower.algebraMap_apply C O κ]
    rfl
  -- the residue point over the unramified extension
  have hcomp : (IsScalarTower.toAlgHom C κ L).comp (IsScalarTower.toAlgHom C O κ) =
      (IsScalarTower.toAlgHom C E L).comp (IsScalarTower.toAlgHom C O E) := by
    ext r
    exact (hρc r).symm
  have hūE : (schemeYoneda _).map ū ≫ a =
      (schemeYoneda _).map (ringTestMap C (IsScalarTower.toAlgHom C E L)) ≫
        uliftYonedaEquiv.symm (RingPoints.changeRing (IsScalarTower.toAlgHom C O E) x) := by
    rw [hū, uliftYonedaEquiv_symm_changeRing, uliftYonedaEquiv_symm_changeRing,
      ← Functor.map_comp_assoc, ← Functor.map_comp_assoc, ← ringTestMap_comp,
      ← ringTestMap_comp, hcomp]
  obtain ⟨uE, huE⟩ := exists_point_of_field_point a ha (O := E) (K := L) hρs
    (RingPoints.changeRing (IsScalarTower.toAlgHom C O E) x) ū hūE
  rw [uliftYonedaEquiv_symm_changeRing] at huE
  -- spread out to rank `D!`
  have hfin : 0 < Module.finrank κ L := Module.finrank_pos
  have hdvd : Module.finrank κ L ∣ D.factorial := Nat.dvd_factorial hfin hdeg
  obtain ⟨k, hk⟩ := hdvd
  let O' := Fin k → E
  let bO : Basis (Fin D.factorial) O O' :=
    ((b.smulTower (Pi.basisFun E (Fin k))).reindex finProdFinEquiv).reindex (finCongr hk.symm)
  let diag : E →ₐ[C] O' := IsScalarTower.toAlgHom C E O'
  refine ⟨O', inferInstance, inferInstance, inferInstance, inferInstance, bO,
    ringTestMap C diag ≫ uE, ?_⟩
  have hdiag : diag.comp (IsScalarTower.toAlgHom C O E) = IsScalarTower.toAlgHom C O O' := by
    ext r
    rfl
  rw [Functor.map_comp_assoc, huE, ← Functor.map_comp_assoc, ← ringTestMap_comp, hdiag]

end Lift

end ProductPointsLocalLift

end Langlands.AlgebraicGeometry.AlgebraicSpace
