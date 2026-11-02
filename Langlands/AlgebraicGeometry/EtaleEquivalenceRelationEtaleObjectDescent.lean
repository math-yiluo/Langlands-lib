import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationStableSystem
import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationActionApproximation
import Mathlib.RingTheory.Smooth.NoetherianDescent

/-! # Descent of affine étale objects to stable finite levels -/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct Opposite

namespace Langlands.AlgebraicGeometry.EtaleEquivalenceRelation

/-- An affine étale object over an affine scheme has an étale model over a
finitely generated subalgebra of its coordinate ring. -/
lemma exists_fg_etale_object_model {R : Type u} [CommRing R]
    {U P : Scheme.{u}} [IsAffine U] [IsAffine P] [Algebra R Γ(U, ⊤)]
    (p : P ⟶ U) [Etale p] :
    ∃ (S : Subalgebra R Γ(U, ⊤)) (Q : Scheme.{u}) (q : Q ⟶ Spec (CommRingCat.of S))
      (k : P ⟶ Q), S.FG ∧ IsAffine Q ∧ Etale q ∧
      IsPullback k p q (U.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom S.val.toRingHom)) := by
  let := p.appTop.hom.toAlgebra
  have hp : Algebra.Etale Γ(U, ⊤) Γ(P, ⊤) :=
    (HasRingHomProperty.iff_of_isAffine (P := @Etale)).mp inferInstance
  obtain ⟨S, T, instRing, instAlg, hS, hT, ⟨e⟩⟩ :=
    Algebra.Etale.exists_subalgebra_fg R Γ(U, ⊤) Γ(P, ⊤)
  let e' : CommRingCat.of (Γ(U, ⊤) ⊗[S] T) ≅ CommRingCat.of Γ(P, ⊤) :=
    e.symm.toRingEquiv.toCommRingCatIso
  let eS : Spec (CommRingCat.of Γ(P, ⊤)) ≅ Spec (CommRingCat.of (Γ(U, ⊤) ⊗[S] T)) :=
    Scheme.Spec.mapIso e'.op
  let e₁ : Spec (CommRingCat.of (Γ(U, ⊤) ⊗[S] T)) ≅ P := (P.isoSpec ≪≫ eS).symm
  let inR := CommRingCat.ofHom
    (Algebra.TensorProduct.includeRight (R := S) (A := Γ(U, ⊤)) (B := T)).toRingHom
  let inL := CommRingCat.ofHom
    (Algebra.TensorProduct.includeLeftRingHom (R := S) (A := Γ(U, ⊤)) (B := T))
  have hleft : e₁.hom ≫ p ≫ U.isoSpec.hom = Spec.map inL := by
    change (eS.inv ≫ P.isoSpec.inv) ≫ p ≫ U.isoSpec.hom = Spec.map inL
    rw [Category.assoc, ← Scheme.isoSpec_hom_naturality, Iso.inv_hom_id_assoc]
    rw [show eS.inv = Spec.map e'.inv from rfl, ← Spec.map_comp]
    congr 1
    ext a
    exact e.commutes a
  refine ⟨S, Spec (CommRingCat.of T), Spec.map (CommRingCat.ofHom (algebraMap S T)),
    e₁.inv ≫ Spec.map inR, hS, inferInstance, ?_, ?_⟩
  · exact (HasRingHomProperty.Spec_iff (P := @Etale)).mpr
      (RingHom.etale_algebraMap.mpr hT)
  · have H := (isPullback_SpecMap_of_isPushout _ _ _ _
      (CommRingCat.isPushout_tensorProduct S Γ(U, ⊤) T)).flip
    refine H.of_iso e₁ (Iso.refl _) U.isoSpec.symm (Iso.refl _) ?_ ?_ (by simp)
      (by simp; rfl)
    · simp
      rfl
    · apply (cancel_mono U.isoSpec.hom).1
      simpa only [Iso.symm_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id] using hleft.symm

namespace IsCartesianHom

open RingEtaleGroupoid

variable {E E₀ : EtaleEquivalenceRelation.{u}} {f : E.U ⟶ E₀.U} {g : E.R ⟶ E₀.R}
  (h : IsCartesianHom E E₀ f g) [IsAffine E.U] [IsAffine E₀.U] [IsAffine E₀.R]
  [IsNoetherianRing Γ(E₀.U, ⊤)]

/-- An affine étale object descends to an étale object at a stable finite level. -/
lemma exists_stable_etale_object_model {P : Scheme.{u}} [IsAffine P]
    (p : P ⟶ E.U) [Etale p] :
    ∃ (i : (h.stableIndex)ᵒᵖ) (Pi : Scheme.{u}) (pi : Pi ⟶ (h.stableDiagram.obj i).U)
      (li : P ⟶ Pi), IsAffine Pi ∧ Etale pi ∧
        IsPullback li p pi (h.stableCone.π.app i).objMap := by
  let := E₀.s.appTop.hom.toAlgebra
  let := f.appTop.hom.toAlgebra
  obtain ⟨S, Q, q, k, hS, hQ, hq, H⟩ :=
    exists_fg_etale_object_model (R := Γ(E₀.U, ⊤)) p
  let := hQ
  let := hq
  obtain ⟨i, hi⟩ := StableSystem.exists_ge E₀.ringEtaleGroupoid h.coaction
    h.coaction_isMultiplicative S hS
  let v : (h.stableDiagram.obj (op i)).U ⟶ Spec (CommRingCat.of S) :=
    Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hi).toRingHom)
  let ci : E.U ⟶ (h.stableDiagram.obj (op i)).U := (h.stableCone.π.app (op i)).objMap
  have hcomp : ci ≫ v =
      E.U.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom S.val.toRingHom) := by
    change (E.U.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom i.1.val.toRingHom)) ≫
      Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hi).toRingHom) = _
    rw [Category.assoc, ← Spec.map_comp]
    rfl
  let Pi := pullback q v
  let pi : Pi ⟶ (h.stableDiagram.obj (op i)).U := pullback.snd q v
  let li : P ⟶ Pi := pullback.lift k (p ≫ ci) (by
    rw [Category.assoc, hcomp]
    exact H.w)
  have hright : IsPullback (pullback.fst q v) pi q v := IsPullback.of_hasPullback q v
  have houter : IsPullback (li ≫ pullback.fst q v) p q (ci ≫ v) := by
    simpa only [li, pullback.lift_fst, hcomp] using H
  have hleft : IsPullback li p pi ci :=
    houter.of_right (by simp [li, pi]) hright
  have : Etale pi := MorphismProperty.of_isPullback hright inferInstance
  exact ⟨op i, Pi, pi, li, inferInstance, inferInstance, hleft⟩

/-- An action on an affine étale object descends equivariantly to a stable
finite level, and its structural morphism remains étale. -/
lemma exists_stable_etale_action_model {P : Scheme.{u}} [IsAffine P]
    (p : P ⟶ E.U) [Etale p] (A : Action E p) :
    ∃ (i : (h.stableIndex)ᵒᵖ) (Pi : Scheme.{u}) (pi : Pi ⟶ (h.stableDiagram.obj i).U)
      (li : P ⟶ Pi) (B : Action (h.stableDiagram.obj i) pi)
      (hi : IsPullback li p pi (h.stableCone.π.app i).objMap),
      IsAffine Pi ∧ Etale pi ∧
        Action.IsEquivariant (h.stableCone.π.app i).isCartesian p pi li hi.w.symm A B := by
  let := h.stableIndex_isCofiltered
  obtain ⟨j, Q, q, k, hQ, hq, hp⟩ := h.exists_stable_etale_object_model p
  let := hQ
  let := hq
  let D := h.stableDiagram
  let Dj := CartesianDiagram.above D j
  let tj := CartesianDiagram.comparison D j
  let cj := h.stableCone.whisker (Over.forget j)
  have hm : ∀ a, cj.π.app a ≫ tj.app a = h.stableCone.π.app j := by
    intro a
    exact h.stableCone.w a.hom
  have (a : Over j) : IsAffine (Dj.obj a).U :=
    show IsAffine (D.obj a.left).U from inferInstance
  have (a : Over j) : IsAffine (Dj.obj a).R :=
    show IsAffine (D.obj a.left).R from inferInstance
  obtain ⟨a, Pi, pi, li, ki, B, hi, hpi, _, hB⟩ :=
    Action.CartesianSystem.exists_equivariant_action_at_level Dj tj cj
      (h.stableCone.π.app j) hm hp
      (CartesianDiagram.isLimitObjectAbove D j h.stableCone h.stableCone_isLimitObject) A
  have : Etale pi := MorphismProperty.of_isPullback hpi inferInstance
  have : IsAffineHom pi := MorphismProperty.of_isPullback hpi inferInstance
  have : IsAffine Pi := isAffine_of_isAffineHom pi
  exact ⟨a.left, Pi, pi, li, B, hi, inferInstance, inferInstance, hB⟩

/-- The data of an affine étale action model at one stable finite level. -/
structure StableEtaleActionModel {P : Scheme.{u}} (p : P ⟶ E.U) (A : Action E p) where
  index : (h.stableIndex)ᵒᵖ
  object : Scheme.{u}
  projection : object ⟶ (h.stableDiagram.obj index).U
  comparison : P ⟶ object
  action : Action (h.stableDiagram.obj index) projection
  square : IsPullback comparison p projection (h.stableCone.π.app index).objMap
  affine : IsAffine object
  etale : Etale projection
  equivariant : Action.IsEquivariant (h.stableCone.π.app index).isCartesian p projection
    comparison square.w.symm A action

/-- Choose a descended affine étale action at a stable finite level. -/
noncomputable def stableEtaleActionModel {P : Scheme.{u}} [IsAffine P]
    (p : P ⟶ E.U) [Etale p] (A : Action E p) : h.StableEtaleActionModel p A := by
  apply Classical.choice
  obtain ⟨i, Pi, pi, li, B, hi, hPi, hpi, hB⟩ :=
    h.exists_stable_etale_action_model p A
  exact ⟨⟨i, Pi, pi, li, B, hi, hPi, hpi, hB⟩⟩

end IsCartesianHom

end Langlands.AlgebraicGeometry.EtaleEquivalenceRelation
