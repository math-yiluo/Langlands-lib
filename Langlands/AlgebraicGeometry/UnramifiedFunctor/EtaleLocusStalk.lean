import Langlands.AlgebraicGeometry.UnramifiedFunctor.EtaleLocusBasic

/-! # Points of a scheme over `Spec D` through its stalks

For a scheme `X` with a morphism `q : X ⟶ Spec D`, the ring map `D → 𝒪_{X,x}` (`structMap`),
its compatibility with `Spec 𝒪_{X,x} ⟶ X`, with specialization and with points
`Spec C ⟶ X` of local rings, and its formal unramifiedness when `q` is formally unramified.
Also a version of `Charts.elemEquiv_naturality` without the monomorphism hypothesis. -/

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite IsLocalRing

noncomputable section

namespace Langlands.AlgebraicGeometry.UnramifiedFunctor

namespace EtaleLocus

section Stalk

variable {X : Scheme.{u}}

/-- Two local ring maps out of a stalk with the same composite to `X` are equal. -/
lemma specMap_fromSpecStalk_injective {x : X} {C : CommRingCat.{u}} [IsLocalRing C]
    (χ₁ χ₂ : X.presheaf.stalk x ⟶ C) [IsLocalHom χ₁.hom] [IsLocalHom χ₂.hom]
    (h : Spec.map χ₁ ≫ X.fromSpecStalk x = Spec.map χ₂ ≫ X.fromSpecStalk x) : χ₁ = χ₂ := by
  have h' : (⟨x, ⟨χ₁, inferInstance⟩⟩ :
      Σ x, { f : X.presheaf.stalk x ⟶ C // IsLocalHom f.hom }) = ⟨x, ⟨χ₂, inferInstance⟩⟩ :=
    (SpecToEquivOfLocalRing X C).symm.injective h
  rw [Sigma.mk.inj_iff] at h'
  exact congrArg Subtype.val (eq_of_heq h'.2)

/-- A morphism from the spectrum of a local ring to `X` sending the closed point to `x` is
`Spec χ` followed by `Spec 𝒪_{X,x} ⟶ X`, for a local ring map `χ`. -/
lemma exists_eq_specMap_fromSpecStalk {C : CommRingCat.{u}} [IsLocalRing C] (h : Spec C ⟶ X)
    (x : X) (hx : h (closedPoint C) = x) :
    ∃ χ : X.presheaf.stalk x ⟶ C, IsLocalHom χ.hom ∧ Spec.map χ ≫ X.fromSpecStalk x = h := by
  subst hx
  exact ⟨Scheme.stalkClosedPointTo h, inferInstance,
    Scheme.Spec_stalkClosedPointTo_fromSpecStalk h⟩

variable {D : CommRingCat.{u}} (q : X ⟶ Spec D)

/-- The ring map `D → 𝒪_{Spec D, q x}` (the canonical map to the stalk). -/
def toStalkAt (x : X) : D ⟶ (Spec D).presheaf.stalk (q x) :=
  (Scheme.ΓSpecIso D).inv ≫ (Spec D).presheaf.germ ⊤ (q x) trivial

/-- The ring map `D → 𝒪_{X,x}` induced by `q : X ⟶ Spec D`. -/
def structMap (x : X) : D ⟶ X.presheaf.stalk x :=
  toStalkAt q x ≫ q.stalkMap x

lemma specMap_structMap (x : X) : Spec.map (structMap q x) = X.fromSpecStalk x ≫ q := by
  rw [structMap, Spec.map_comp, toStalkAt, ← Spec.fromSpecStalk_eq,
    Scheme.SpecMap_stalkMap_fromSpecStalk]

/-- If `Spec χ` followed by `Spec 𝒪_{X,x} ⟶ X` lies over `Spec δ`, then `χ ∘ structMap = δ`. -/
lemma structMap_comp_eq (x : X) {C : CommRingCat.{u}} (χ : X.presheaf.stalk x ⟶ C)
    (δ : D ⟶ C) (h : Spec.map χ ≫ X.fromSpecStalk x ≫ q = Spec.map δ) :
    structMap q x ≫ χ = δ := by
  apply Spec.map_inj.1
  rw [Spec.map_comp, specMap_structMap, h]

lemma structMap_stalkSpecializes {x y : X} (h : x ⤳ y) :
    structMap q y ≫ X.presheaf.stalkSpecializes h = structMap q x := by
  apply Spec.map_inj.1
  rw [Spec.map_comp, specMap_structMap, specMap_structMap, ← Category.assoc,
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk]

lemma toStalkAt_formallyUnramified (x : X) : (toStalkAt q x).hom.FormallyUnramified := by
  have heq : Spec.map (toStalkAt q x) = Spec.map (StructureSheaf.toStalk D (q x)) := by
    rw [toStalkAt, ← Spec.fromSpecStalk_eq, Spec.fromSpecStalk_eq']
  rw [Spec.map_inj.1 heq]
  have := (q x).isPrime
  let _ : Algebra D ((Spec D).presheaf.stalk (q x)) := StructureSheaf.stalkAlgebra D (q x)
  have : IsLocalization.AtPrime ((Spec D).presheaf.stalk (q x)) (q x).asIdeal :=
    StructureSheaf.IsLocalization.to_stalk D (q x)
  exact RingHom.FormallyUnramified.holdsForLocalization _ (q x).asIdeal.primeCompl

lemma structMap_formallyUnramified [FormallyUnramified q] (x : X) :
    (structMap q x).hom.FormallyUnramified :=
  RingHom.FormallyUnramified.comp (toStalkAt_formallyUnramified q x)
    (FormallyUnramified.stalkMap q x)

end Stalk

section Rep

variable {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type v} {S' : Scheme.{u}} (g : S' ⟶ S)
  {Y' : Over S'} (e : (baseChange g F).RepresentableBy Y')

/-- `Charts.elemEquiv_naturality` with an explicit compatibility instead of `Mono g`. -/
lemma elemEquiv_naturality' {T₁ T₂ : Over S} (h : T₁ ⟶ T₂) (t₁ : T₁.left ⟶ S')
    (t₂ : T₂.left ⟶ S') (ht₁ : t₁ ≫ g = T₁.hom) (ht₂ : t₂ ≫ g = T₂.hom)
    (hc : h.left ≫ t₂ = t₁) (a : Over.mk t₂ ⟶ Y') :
    F.map h.op (Charts.elemEquiv g e T₂ t₂ ht₂ a) =
      Charts.elemEquiv g e T₁ t₁ ht₁
        ((Over.homMk h.left hc : Over.mk t₁ ⟶ Over.mk t₂) ≫ a) := by
  have hcomm : h ≫ (Charts.liftIso g T₂ t₂ ht₂).hom = (Charts.liftIso g T₁ t₁ ht₁).hom ≫
      (Over.map g).map (Over.homMk h.left hc : Over.mk t₁ ⟶ Over.mk t₂) := by
    ext1
    simp [Charts.liftIso]
  rw [Charts.elemEquiv_apply, Charts.elemEquiv_apply, e.homEquiv_comp]
  change (F.map (Charts.liftIso g T₂ t₂ ht₂).hom.op ≫ F.map h.op) (e.homEquiv a) =
    (F.map ((Over.map g).map (Over.homMk h.left hc : Over.mk t₁ ⟶ Over.mk t₂)).op ≫
      F.map (Charts.liftIso g T₁ t₁ ht₁).hom.op) (e.homEquiv a)
  rw [← F.map_comp, ← F.map_comp, ← op_comp, ← op_comp, hcomm]

/-- Composing the element attached to `a` with `h` gives the element attached to `h ≫ a`;
the form used to compare two elements through `elemEquiv`. -/
lemma elemEquiv_symm_naturality {T₁ T₂ : Over S} (h : T₁ ⟶ T₂) (t₁ : T₁.left ⟶ S')
    (t₂ : T₂.left ⟶ S') (ht₁ : t₁ ≫ g = T₁.hom) (ht₂ : t₂ ≫ g = T₂.hom)
    (hc : h.left ≫ t₂ = t₁) (z : F.obj (op T₂)) :
    (Charts.elemEquiv g e T₁ t₁ ht₁).symm (F.map h.op z) =
      (Over.homMk h.left hc : Over.mk t₁ ⟶ Over.mk t₂) ≫
        (Charts.elemEquiv g e T₂ t₂ ht₂).symm z := by
  rw [Equiv.symm_apply_eq, ← elemEquiv_naturality' g e h t₁ t₂ ht₁ ht₂ hc, Equiv.apply_symm_apply]

end Rep

end EtaleLocus

end Langlands.AlgebraicGeometry.UnramifiedFunctor
