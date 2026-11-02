import Langlands.AlgebraicGeometry.Picard.NilpotentUnitReduction
import Mathlib.Topology.Sheaves.Functors
import Mathlib.Topology.Sheaves.Abelian
import Mathlib.CategoryTheory.Limits.Preorder
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.Algebra.Homology.DerivedCategory.Ext.MapAdjunction

/-! # Actual unit sheaves and cohomology under topological pushforward -/

universe u v w

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard.UnitSheafPushforward

open NilpotentUnitReduction

section Units

variable {X Y : TopCat.{u}} (f : X ⟶ Y)

/-- Taking actual units commutes with actual topological pushforward. -/
def unitsPushforwardIso (F : X.Presheaf CommRingCat.{u})
    (hF : TopCat.Presheaf.IsSheaf F) :
    unitsSheaf ((Opens.map f).op ⋙ F)
      (TopCat.Sheaf.pushforward_sheaf_of_sheaf f hF) ≅
        (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj (unitsSheaf F hF) :=
  Iso.refl _

@[simp]
lemma unitsPushforwardIso_hom_app (F : X.Presheaf CommRingCat.{u})
    (hF : TopCat.Presheaf.IsSheaf F) (U : (Opens Y)ᵒᵖ) :
    ((unitsPushforwardIso f F hF).hom.hom.app U) = 𝟙 _ := rfl

end Units

section Sheaves

variable {C : Type v} [Category.{w} C] {X Y : TopCat.{u}} (e : X ≅ Y)

/-- Pushforward along a homeomorphism is an equivalence of actual sheaf categories. -/
def sheafPushforwardEquivalence : X.Sheaf C ≌ Y.Sheaf C :=
  CategoryTheory.Equivalence.mk (TopCat.Sheaf.pushforward C e.hom)
    (TopCat.Sheaf.pushforward C e.inv)
    (NatIso.ofComponents (fun F ↦ ObjectProperty.isoMk _
      ((TopCat.Presheaf.presheafEquivOfIso C e).unitIso.app F.obj)) (by
        intro F G α
        apply CategoryTheory.Sheaf.hom_ext
        exact (TopCat.Presheaf.presheafEquivOfIso C e).unitIso.hom.naturality α.hom))
    (NatIso.ofComponents (fun F ↦ ObjectProperty.isoMk _
      ((TopCat.Presheaf.presheafEquivOfIso C e).counitIso.app F.obj)) (by
        intro F G α
        apply CategoryTheory.Sheaf.hom_ext
        exact (TopCat.Presheaf.presheafEquivOfIso C e).counitIso.hom.naturality α.hom))

end Sheaves

section Cohomology

variable {X Y : TopCat.{u}} (e : X ≅ Y)

/-- The inverse topological pushforward carries a constant sheaf to the same constant sheaf. -/
def constantInversePushforwardIso :
    constantSheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u} ⋙
      TopCat.Sheaf.pushforward AddCommGrpCat.{u} e.inv ≅
        constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} :=
  ((constantSheafAdj (Opens.grothendieckTopology Y) AddCommGrpCat.{u}
    (isTerminalTop (α := Opens Y))).comp
      (sheafPushforwardEquivalence (C := AddCommGrpCat.{u}) e).symm.toAdjunction).leftAdjointUniq
    (constantSheafAdj (Opens.grothendieckTopology X) AddCommGrpCat.{u}
      (isTerminalTop (α := Opens X)))

set_option backward.isDefEq.respectTransparency false in
/-- Pushforward along a homeomorphism preserves all actual abelian-sheaf cohomology groups. -/
def cohomologyPushforwardEquiv (F : X.Sheaf AddCommGrpCat.{u}) (n : ℕ) :
    CategoryTheory.Sheaf.H.{u}
      ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} e.hom).obj F) n ≃+
        CategoryTheory.Sheaf.H.{u} F n := by
  let E := sheafPushforwardEquivalence (C := AddCommGrpCat.{u}) e
  letI : E.functor.IsEquivalence := E.isEquivalence_functor
  letI : E.inverse.IsEquivalence := E.isEquivalence_inverse
  letI : E.functor.Additive := E.functor.additive_of_preserves_binary_products
  letI : E.inverse.Additive := E.inverse.additive_of_preserves_binary_products
  let adj : E.inverse ⊣ E.functor := E.symm.toAdjunction
  let c := (constantInversePushforwardIso e).app (AddCommGrpCat.of (ULift ℤ))
  exact adj.extEquiv.symm.trans
    (Iso.addCommGroupIsoToAddEquiv (((Abelian.extFunctor.{u} n).mapIso c.symm.op).app F))

set_option backward.isDefEq.respectTransparency false in
/-- The cohomology of actual units of a pushed-forward ring sheaf is unchanged by a homeomorphism. -/
def unitsCohomologyPushforwardEquiv (F : X.Presheaf CommRingCat.{u})
    (hF : TopCat.Presheaf.IsSheaf F) (n : ℕ) :
    CategoryTheory.Sheaf.H.{u} (unitsSheaf ((Opens.map e.hom).op ⋙ F)
      (TopCat.Sheaf.pushforward_sheaf_of_sheaf e.hom hF)) n ≃+
        CategoryTheory.Sheaf.H.{u} (unitsSheaf F hF) n :=
  cohomologyPushforwardEquiv e (unitsSheaf F hF) n

end Cohomology

section Schemes

variable {X Y : Scheme.{u}} (i : Y ⟶ X) [IsClosedImmersion i]

/-- A closed immersion with nilpotent ideal sheaf is surjective on the underlying space. -/
lemma nilpotentClosedImmersion_surjective (hi : IsNilpotent i.ker) : Function.Surjective i := by
  obtain ⟨n, hn⟩ := hi
  have hsupport : i.ker.support = ⊤ := by
    rw [← i.ker.support_pow_succ n, pow_succ, hn, zero_mul]
    exact Scheme.IdealSheafData.support_bot
  have hrange : Set.range i = Set.univ := by
    have h := i.support_ker
    rw [i.isClosedEmbedding.isClosed_range.closure_eq, hsupport] at h
    exact h.symm
  exact Set.range_eq_univ.mp hrange

/-- The actual underlying homeomorphism of a nilpotent closed immersion. -/
def nilpotentClosedImmersionTopIso (hi : IsNilpotent i.ker) : Y.toTopCat ≅ X.toTopCat :=
  TopCat.isoOfHomeo (isHomeomorph_iff_isEmbedding_surjective.mpr
    ⟨i.isClosedEmbedding.isEmbedding, nilpotentClosedImmersion_surjective i hi⟩).homeomorph

@[simp]
lemma nilpotentClosedImmersionTopIso_hom (hi : IsNilpotent i.ker) :
    (nilpotentClosedImmersionTopIso i hi).hom = i.base := rfl

set_option backward.isDefEq.respectTransparency false in
/-- Actual structure-unit cohomology on a nilpotent closed subscheme agrees with its pushforward. -/
def nilpotentUnitsCohomologyPushforwardEquiv (hi : IsNilpotent i.ker) (n : ℕ) :
    CategoryTheory.Sheaf.H.{u} (unitsSheaf ((Opens.map i.base).op ⋙ Y.presheaf)
      (TopCat.Sheaf.pushforward_sheaf_of_sheaf i.base Y.sheaf.property)) n ≃+
        CategoryTheory.Sheaf.H.{u} (unitsSheaf Y.presheaf Y.sheaf.property) n :=
  unitsCohomologyPushforwardEquiv (nilpotentClosedImmersionTopIso i hi)
    Y.presheaf Y.sheaf.property n

end Schemes

end Langlands.AlgebraicGeometry.Picard.UnitSheafPushforward
