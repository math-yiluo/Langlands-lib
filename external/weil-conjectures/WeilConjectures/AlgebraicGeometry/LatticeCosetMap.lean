/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.LatticeSheafBasic
public import Mathlib.CategoryTheory.Sites.LocallyBijective
import WeilConjectures.CategoryTheory.LargeSetSheafification

/-!
# The constant matrix map to lattice classes

Source: Bhatt--Scholze, Proposition 6.8.4(6), pp. 59--60
(auxiliary; not a blueprint node).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

variable (X : Scheme.{u}) (K : Type u) [Field K]
  [TopologicalSpace K] [IsTopologicalRing K] (A : Subring K)

variable (L : SheafOfModules.{u + 1} (latticeModuleRing X K))
  (F : Sheaf (Scheme.ProEt.topology X) (Type (u + 2)))
  (c : ∀ V : X.ProEt,
    IntegralLatticePair (latticeCoefficientSheafMap X A.subtype continuous_subtype_val) L V →
      F.obj.obj (op V))
  (hc : IsLatticeClassPresentation
    (latticeCoefficientSheafMap X A.subtype continuous_subtype_val) L F c)
  (U : X.ProEt) (n : ℕ) (e : L.over U ≅ latticeFreeSheaf X K U n)

/-- A representative of the constant matrix lattice, chosen from the proved explicit construction.
Source: Bhatt--Scholze, Proposition 6.8.4(6), construction of g A^n
(auxiliary; not a blueprint node). -/
noncomputable def matrixLatticePair (g : Matrix.GeneralLinearGroup (Fin n) K) :
    IntegralLatticePair (latticeCoefficientSheafMap X A.subtype continuous_subtype_val) L U :=
  (exists_matrixIntegralLatticePair X K A U n L e g).choose

/-- The chosen pair has exactly the prescribed matrix lattice image.
Source: Bhatt--Scholze, Proposition 6.8.4(6), construction of g A^n
(auxiliary; not a blueprint node).
Proof: this is the specification of the proved construction used to choose the pair. -/
theorem matrixLatticePair_image (g : Matrix.GeneralLinearGroup (Fin n) K)
    (T : (Over U)ᵒᵖ) :
    Set.image (e.hom.val.app T) ((matrixLatticePair X K A L U n e g).image T) =
      matrixLatticeImage X K A U n g T :=
  (exists_matrixIntegralLatticePair X K A U n L e g).choose_spec T

include hc

/-- The class of a constant matrix lattice is characterized by its embedded images.
Source: Bhatt--Scholze, Proposition 6.8.4(6), comparison of embedded lattices
(auxiliary; not a blueprint node).
Proof: equality of classes is equivalence of pairs, which is equality of all images.
Apply the injective rational trivialization and the formula for the constant matrix pair. -/
theorem matrixLatticePair_class_eq_iff (g : Matrix.GeneralLinearGroup (Fin n) K)
    (P : IntegralLatticePair (latticeCoefficientSheafMap X A.subtype continuous_subtype_val) L U) :
    c U (matrixLatticePair X K A L U n e g) = c U P ↔
      ∀ T : (Over U)ᵒᵖ, Set.image (e.hom.val.app T) (P.image T) =
        matrixLatticeImage X K A U n g T := by
  have ha (T : (Over U)ᵒᵖ) : Function.Injective
      (((latticeScalarMap (latticeCoefficientSheafMap X A.subtype
        continuous_subtype_val) U).hom.app T).hom) := by
    intro f g h
    apply ULift.ext
    apply ContinuousMap.ext
    intro x
    apply Subtype.ext
    exact congrArg (fun s ↦ s.down x) h
  rw [hc.2.1, IntegralLatticePair.equivalent_iff_image_eq _ L U ha]
  constructor
  · intro h T
    rw [← h T, matrixLatticePair_image]
  · intro h T
    apply Set.image_injective.mpr
      (((SheafOfModules.evaluation _ T).mapIso e).toLinearEquiv.injective)
    exact (matrixLatticePair_image X K A L U n e g T).trans (h T).symm

/-- The constant lattice class depends only on the integral matrix coset.
Source: Bhatt--Scholze, Proposition 6.8.4(6), integral change of basis
(auxiliary; not a blueprint node).
Proof: equal cosets have equal matrix images, so the image criterion identifies their classes. -/
theorem matrixLatticePair_class_eq (g h : Matrix.GeneralLinearGroup (Fin n) K)
    (hgh : (Quotient.mk _ g : integralMatrixCosets A n) = Quotient.mk _ h) :
    c U (matrixLatticePair X K A L U n e g) =
      c U (matrixLatticePair X K A L U n e h) := by
  apply (matrixLatticePair_class_eq_iff X K A L F c hc U n e g _).mpr
  intro T
  exact (matrixLatticePair_image X K A L U n e h T).trans
    (matrixLatticeImage_eq_of_coset_eq X K A U n g h hgh T).symm

/-- The quotient map from integral matrix cosets to lattice classes over a trivializing object.
Source: Bhatt--Scholze, Proposition 6.8.4(6), the constant-coset map
(auxiliary; not a blueprint node). -/
noncomputable def latticeCosetSection : integralMatrixCosets A n → F.obj.obj (op U) :=
  Quotient.lift (fun g ↦ c U (matrixLatticePair X K A L U n e g))
    (fun g h hgh ↦ matrixLatticePair_class_eq X K A L F c hc U n e g h
      (Quotient.sound hgh))

/-- Restrict the constant matrix classes to obtain a map on the entire slice site.
Source: Bhatt--Scholze, Proposition 6.8.4(6), the constant-presheaf map
(auxiliary; not a blueprint node). -/
noncomputable def latticeCosetMap :
    (Functor.const (Over U)ᵒᵖ).obj (ULift.{u + 2} (integralMatrixCosets A n)) ⟶
      (F.over U).obj where
  app T := TypeCat.ofHom fun q ↦ F.obj.map T.unop.hom.op
    (latticeCosetSection X K A L F c hc U n e q.down)
  naturality T T' f := by
    ext q
    change F.obj.map T'.unop.hom.op _ =
      F.obj.map f.unop.left.op (F.obj.map T.unop.hom.op _)
    rw [← F.obj.map_comp_apply, ← op_comp, Over.w]
    rfl

/-- On the identity object, the constant-presheaf map has the required normalization.
Source: Bhatt--Scholze, Proposition 6.8.4(6), identification of constant cosets
(auxiliary; not a blueprint node).
Proof: restriction along the identity is the identity. Apply the image criterion for classes. -/
theorem latticeCosetMap_normalization (g : Matrix.GeneralLinearGroup (Fin n) K)
    (P : IntegralLatticePair (latticeCoefficientSheafMap X A.subtype continuous_subtype_val) L U) :
    (latticeCosetMap X K A L F c hc U n e).app (op (Over.mk (𝟙 U)))
        (ULift.up (Quotient.mk _ g)) = c U P ↔
      ∀ T : (Over U)ᵒᵖ, Set.image (e.hom.val.app T) (P.image T) =
        matrixLatticeImage X K A U n g T := by
  change F.obj.map (𝟙 U).op (c U (matrixLatticePair X K A L U n e g)) = _ ↔ _
  rw [op_id, F.obj.map_id]
  exact matrixLatticePair_class_eq_iff X K A L F c hc U n e g P

/-- Restricted constant classes are detected by the rationally transported lattice images.
Source: Bhatt--Scholze, Proposition 6.8.4(6), restriction of embedded lattices
(auxiliary; not a blueprint node).
Proof: represent the restriction of the pair by a pair Q. The class presentation
identifies its images with those of P on every further restriction. Apply the same
restriction criterion to the constant matrix pair and use injectivity of the rational
trivialization to cancel its application to the two image sets. -/
theorem latticeCosetMap_eq_restrict_iff (V W : X.ProEt) (f : V ⟶ U) (a : W ⟶ V)
    (P : IntegralLatticePair (latticeCoefficientSheafMap X A.subtype continuous_subtype_val)
      L V) (g : Matrix.GeneralLinearGroup (Fin n) K) :
    (latticeCosetMap X K A L F c hc U n e).app (op (Over.mk (a ≫ f)))
        (ULift.up (Quotient.mk _ g)) = F.obj.map a.op (c V P) ↔
      ∀ T : Over W,
        Set.image (e.hom.val.app (op (Over.mk (T.hom ≫ a ≫ f))))
          (P.image (op (Over.mk (T.hom ≫ a)))) =
        matrixLatticeImage X K A U n g (op (Over.mk (T.hom ≫ a ≫ f))) := by
  obtain ⟨Q, hQ⟩ := hc.1 W (F.obj.map a.op (c V P))
  have hP := (hc.2.2 V W a P Q).mp hQ.symm
  change F.obj.map (a ≫ f).op (c U (matrixLatticePair X K A L U n e g)) = _ ↔ _
  rw [← hQ, hc.2.2]
  constructor
  · intro h T
    have hh := (h T).trans (hP T).symm
    have hi := congrArg (Set.image (e.hom.val.app
      (op (Over.mk (T.hom ≫ a ≫ f))))) hh
    change Set.image _ ((matrixLatticePair X K A L U n e g).image
      (op (Over.mk (T.hom ≫ a ≫ f)))) = _ at hi
    rw [matrixLatticePair_image] at hi
    exact hi.symm
  · intro h T
    have hi := h T
    rw [← matrixLatticePair_image X K A L U n e g] at hi
    let ev := SheafOfModules.evaluation ((latticeModuleRing X K).over U)
      (op (Over.mk (T.hom ≫ a ≫ f)))
    have hh := Set.image_injective.mpr (ev.mapIso e).toLinearEquiv.injective hi
    exact hh.symm.trans (hP T)

/-- Equality of two restricted constant matrix classes over a nonempty object detects the coset.
Source: Bhatt--Scholze, Proposition 6.8.4(6), evaluation of constant lattices
(auxiliary; not a blueprint node).
Proof: represent the common restricted class by a lattice pair. The restriction clause
of the class presentation identifies both original images with that pair's image on
all further slice objects. Apply the rational trivialization and evaluate at a point. -/
theorem latticeCosetMap_injective_at (T : (Over U)ᵒᵖ)
    (hT : Nonempty T.unop.left.left) :
    Function.Injective ((latticeCosetMap X K A L F c hc U n e).app T) := by
  rintro ⟨q⟩ ⟨r⟩ hqr
  apply ULift.ext
  induction q, r using Quotient.inductionOn₂ with
  | h g h =>
    change F.obj.map T.unop.hom.op (c U (matrixLatticePair X K A L U n e g)) =
      F.obj.map T.unop.hom.op (c U (matrixLatticePair X K A L U n e h)) at hqr
    obtain ⟨Q, hQ⟩ := hc.1 T.unop.left
      (F.obj.map T.unop.hom.op (c U (matrixLatticePair X K A L U n e g)))
    have hg := (hc.2.2 U T.unop.left T.unop.hom
      (matrixLatticePair X K A L U n e g) Q).mp hQ.symm
    have hh := (hc.2.2 U T.unop.left T.unop.hom
      (matrixLatticePair X K A L U n e h) Q).mp (hqr.symm.trans hQ.symm)
    apply matrixLatticeImage_coset_eq_of_eq_at X K A U n g h T hT
    rw [← matrixLatticePair_image X K A L U n e g T,
      ← matrixLatticePair_image X K A L U n e h T]
    congr 1
    have hi := (hg (Over.mk (𝟙 T.unop.left))).trans
      (hh (Over.mk (𝟙 T.unop.left))).symm
    have ht : (Over.map T.unop.hom).obj (Over.mk (𝟙 T.unop.left)) = T.unop := by
      cases T with
      | op T =>
        cases T with
        | mk left right hom =>
          cases right with
          | mk right =>
            cases right
            change Over.mk (𝟙 left ≫ hom) = _
            rw [Category.id_comp]
            rfl
    rw [ht] at hi
    exact hi

/-- The constant-coset presheaf map is locally injective, including on empty objects.
Source: Bhatt--Scholze, Proposition 6.8.4(6), injectivity of the coset map
(auxiliary; not a blueprint node).
Proof: at a nonempty test object the preceding evaluation argument gives injectivity,
so the equalizer sieve is maximal. At an empty object the empty sieve covers, hence
its containing equalizer sieve covers as well. -/
theorem latticeCosetMap_locallyInjective :
    Presheaf.IsLocallyInjective ((Scheme.ProEt.topology X).over U)
      (latticeCosetMap X K A L F c hc U n e) := by
  constructor
  intro T q r hqr
  by_cases hT : Nonempty T.unop.left.left
  · have h := latticeCosetMap_injective_at X K A L F c hc U n e T hT hqr
    subst r
    rw [Presheaf.equalizerSieve_self_eq_top]
    exact ((Scheme.ProEt.topology X).over U).top_mem _
  · let : IsEmpty T.unop.left.left := not_nonempty_iff.mp hT
    apply ((Scheme.ProEt.topology X).over U).superset_covering bot_le
    rw [GrothendieckTopology.mem_over_iff]
    simpa using Scheme.ProEt.bot_mem_topology T.unop.left

/-- The extension of the constant matrix map to the constant sheaf.
Source: Bhatt--Scholze, Proposition 6.8.4(6), sheafification of the coset map
(auxiliary; not a blueprint node). -/
noncomputable def latticeCosetSheafMap :
    (constantSheaf ((Scheme.ProEt.topology X).over U) (Type (u + 2))).obj
      (ULift.{u + 2} (integralMatrixCosets A n)) ⟶ F.over U :=
  ⟨sheafifyLift ((Scheme.ProEt.topology X).over U)
    (latticeCosetMap X K A L F c hc U n e) (F.over U).property⟩

/-- The extension agrees with the constant-presheaf map on the sheafification unit.
Source: Bhatt--Scholze, Proposition 6.8.4(6), sheafification of the coset map
(auxiliary; not a blueprint node).
Proof: apply the universal property of sheafification to the constructed map. -/
theorem latticeCosetSheafMap_unit (T : (Over U)ᵒᵖ)
    (q : ULift.{u + 2} (integralMatrixCosets A n)) :
    (latticeCosetSheafMap X K A L F c hc U n e).hom.app T
        ((toSheafify ((Scheme.ProEt.topology X).over U)
          ((Functor.const (Over U)ᵒᵖ).obj
            (ULift.{u + 2} (integralMatrixCosets A n)))).app T q) =
      (latticeCosetMap X K A L F c hc U n e).app T q := by
  exact congrArg (fun f ↦ f.app T q)
    (toSheafify_sheafifyLift ((Scheme.ProEt.topology X).over U)
      (latticeCosetMap X K A L F c hc U n e) (F.over U).property)

/-- The sheafified constant matrix map retains the full embedded-image normalization.
Source: Bhatt--Scholze, Proposition 6.8.4(6), normalization of the coset comparison
(auxiliary; not a blueprint node).
Proof: the sheafification-unit identity reduces to the normalization of the presheaf map. -/
theorem latticeCosetSheafMap_normalization (g : Matrix.GeneralLinearGroup (Fin n) K)
    (P : IntegralLatticePair (latticeCoefficientSheafMap X A.subtype continuous_subtype_val)
      L U) :
    (latticeCosetSheafMap X K A L F c hc U n e).hom.app (op (Over.mk (𝟙 U)))
        ((toSheafify ((Scheme.ProEt.topology X).over U)
          ((Functor.const (Over U)ᵒᵖ).obj (ULift.{u + 2} (integralMatrixCosets A n)))).app
            (op (Over.mk (𝟙 U))) (ULift.up (Quotient.mk _ g))) = c U P ↔
      ∀ T : (Over U)ᵒᵖ, Set.image (e.hom.val.app T) (P.image T) =
        matrixLatticeImage X K A U n g T := by
  rw [latticeCosetSheafMap_unit]
  exact latticeCosetMap_normalization X K A L F c hc U n e g P

/-- Local surjectivity is the only remaining condition for the normalized coset comparison.
Source: Bhatt--Scholze, Proposition 6.8.4(6), locally bijective comparison
(auxiliary; not a blueprint node).
Proof: the constant-presheaf map is already locally injective. Its sheafification
unit is locally bijective. The factorization through that unit therefore makes
its extension locally bijective, hence an isomorphism of sheaves. -/
theorem latticeCosetSheafMap_isIso
    (hsurj : Presheaf.IsLocallySurjective ((Scheme.ProEt.topology X).over U)
      (latticeCosetMap X K A L F c hc U n e)) :
    IsIso (latticeCosetSheafMap X K A L F c hc U n e) := by
  let J := (Scheme.ProEt.topology X).over U
  let P := (Functor.const (Over U)ᵒᵖ).obj
    (ULift.{u + 2} (integralMatrixCosets A n))
  let η := toSheafify J P
  let m := latticeCosetSheafMap X K A L F c hc U n e
  let : J.WEqualsLocallyBijective (Type (u + 2)) :=
    largeSetSheafification_locallyBijective.{u + 1, u, u + 2} J
  have hfac : η ≫ m.hom = latticeCosetMap X K A L F c hc U n e :=
    toSheafify_sheafifyLift J _ (F.over U).property
  let : Presheaf.IsLocallyInjective J (η ≫ m.hom) :=
    hfac.symm ▸ latticeCosetMap_locallyInjective X K A L F c hc U n e
  let : Presheaf.IsLocallySurjective J (η ≫ m.hom) := hfac.symm ▸ hsurj
  let : Presheaf.IsLocallyInjective J m.hom :=
    Presheaf.isLocallyInjective_of_isLocallyInjective_of_isLocallySurjective J η m.hom
  let : Presheaf.IsLocallySurjective J m.hom :=
    Presheaf.isLocallySurjective_of_isLocallySurjective J η m.hom
  apply (Sheaf.isLocallyBijective_iff_isIso m).mp
  constructor <;> infer_instance

end AlgebraicGeometry.ProEtale
