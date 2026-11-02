import Langlands.AlgebraicGeometry.GroupoidCoactionInvariantIdeal
import Langlands.AlgebraicGeometry.RingEtaleEquivalenceRelationQuotient
import Mathlib.AlgebraicGeometry.Geometrically.Reduced
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.RingTheory.Unramified.Field

/-! # Radical invariant ideals of Noetherian affine étale relations -/

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry

namespace EtaleReduced

/-- An étale scheme over a field is reduced. -/
theorem isReduced_of_etale_to_field {X : Scheme.{u}} (K : Type u) [Field K]
    (f : X ⟶ Spec (CommRingCat.of K)) [Etale f] : AlgebraicGeometry.IsReduced X := by
  let : Field Γ(Spec (CommRingCat.of K), ⊤) :=
    ((Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.toMulEquiv.isField
      (Field.toIsField K)).toField
  have (i : X.affineCover.I₀) : IsReduced (X.affineCover.X i) := by
    let g := X.affineCover.f i ≫ f
    have hg : g.appTop.hom.Etale :=
      (HasRingHomProperty.iff_of_isAffine (P := @Etale) (f := g)).mp inferInstance
    let : Algebra Γ(Spec (CommRingCat.of K), ⊤) Γ(X.affineCover.X i, ⊤) :=
      g.appTop.hom.toAlgebra
    let : Algebra.Etale Γ(Spec (CommRingCat.of K), ⊤) Γ(X.affineCover.X i, ⊤) :=
      hg.toAlgebra
    let : _root_.IsReduced Γ(X.affineCover.X i, ⊤) :=
      Algebra.FormallyUnramified.isReduced_of_field Γ(Spec (CommRingCat.of K), ⊤) _
    exact isReduced_of_isAffine_isReduced (X.affineCover.X i)
  exact IsReduced.of_openCover X X.affineCover

/-- Étale morphisms have geometrically reduced fibers. -/
theorem geometricallyReduced_of_etale {X Y : Scheme.{u}} (f : X ⟶ Y) [Etale f] :
    GeometricallyReduced f := by
  constructor
  intro K _ y Z fst snd h
  let : Etale snd := MorphismProperty.of_isPullback h inferInstance
  exact isReduced_of_etale_to_field K snd

/-- An étale algebra over a reduced Noetherian ring is reduced. -/
theorem isReduced_of_etale_algebra (B C : Type u) [CommRing B] [CommRing C]
    [Algebra B C] [IsNoetherianRing B] [_root_.IsReduced B] [Algebra.Etale B C] :
    _root_.IsReduced C := by
  let f : Spec (CommRingCat.of C) ⟶ Spec (CommRingCat.of B) :=
    Spec.map (CommRingCat.ofHom (algebraMap B C))
  let : Etale f := (HasRingHomProperty.Spec_iff (P := @Etale)).mpr
    (RingHom.etale_algebraMap.mpr inferInstance)
  let : GeometricallyReduced f := geometricallyReduced_of_etale f
  have : AlgebraicGeometry.IsReduced (Spec (CommRingCat.of C)) :=
    GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian f
  exact (affine_isReduced_iff (CommRingCat.of C)).mp this

/-- Étale extension preserves radical ideals over a Noetherian base. -/
theorem isRadical_map_of_etale {B C : Type u} [CommRing B] [CommRing C]
    [IsNoetherianRing B] (f : B →+* C) (hf : f.Etale) (I : Ideal B)
    (hI : I.IsRadical) : (I.map f).IsRadical := by
  let : Algebra B C := f.toAlgebra
  let : _root_.IsReduced (B ⧸ I) := (Ideal.isRadical_iff_quotient_reduced I).mp hI
  have hq := RingEtaleEquivalenceRelation.etale_quotientMap f hf I
  change (algebraMap (B ⧸ I) (C ⧸ I.map (algebraMap B C))).Etale at hq
  let : Algebra.Etale (B ⧸ I) (C ⧸ I.map (algebraMap B C)) :=
    RingHom.etale_algebraMap.mp hq
  exact (Ideal.isRadical_iff_quotient_reduced (I.map f)).mpr
    (isReduced_of_etale_algebra (B ⧸ I) (C ⧸ I.map (algebraMap B C)))

/-- Radical and étale extension commute over a Noetherian base. -/
theorem map_radical_of_etale {B C : Type u} [CommRing B] [CommRing C]
    [IsNoetherianRing B] (f : B →+* C) (hf : f.Etale) (I : Ideal B) :
    I.radical.map f = (I.map f).radical := by
  apply le_antisymm (Ideal.map_radical_le f)
  have hrad := isRadical_map_of_etale f hf I.radical (Ideal.radical_isRadical I)
  exact (Ideal.radical_mono (Ideal.map_mono Ideal.le_radical)).trans_eq hrad.radical

end EtaleReduced

namespace GroupoidCoaction

variable {B C : Type u} [CommRing B] [CommRing C] [Algebra B C]
  [IsNoetherianRing B] {t : B →+* C}

/-- The radical of an invariant ideal is invariant. -/
theorem IsInvariantIdeal.radical (hE : RingEtaleEquivalenceRelation t)
    {I : Ideal B} (hI : IsInvariantIdeal t I) : IsInvariantIdeal t I.radical := by
  change I.radical.map t = I.radical.map (algebraMap B C)
  rw [EtaleReduced.map_radical_of_etale t hE.etale_t,
    EtaleReduced.map_radical_of_etale (algebraMap B C) hE.etale_algebraMap, hI]

/-- The reduced closed support of a finite coaction is defined by an invariant ideal. -/
theorem radical_annihilator_isInvariantIdeal {M : Type v} [AddCommGroup M]
    [Module B M] [Module.Finite B M] (hE : RingEtaleEquivalenceRelation t)
    (θ : GroupoidCoaction t M) : IsInvariantIdeal t (Module.annihilator B M).radical := by
  let : Module.FinitePresentation B M := Module.finitePresentation_of_finite B M
  exact (annihilator_isInvariantIdeal hE θ).radical hE

/-- The radical invariant ideal of the reduced closed support of a finite
coaction, with both properties recorded in its type. -/
noncomputable def reducedSupportInvariantIdeal {M : Type v} [AddCommGroup M]
    [Module B M] [Module.Finite B M] (hE : RingEtaleEquivalenceRelation t)
    (θ : GroupoidCoaction t M) :
    {I : Ideal B // I.IsRadical ∧ IsInvariantIdeal t I} :=
  ⟨(Module.annihilator B M).radical, Ideal.radical_isRadical _,
    radical_annihilator_isInvariantIdeal hE θ⟩

@[simp]
lemma reducedSupportInvariantIdeal_val {M : Type v} [AddCommGroup M]
    [Module B M] [Module.Finite B M] (hE : RingEtaleEquivalenceRelation t)
    (θ : GroupoidCoaction t M) :
    (reducedSupportInvariantIdeal hE θ).val = (Module.annihilator B M).radical := rfl

end GroupoidCoaction

end Langlands.AlgebraicGeometry
