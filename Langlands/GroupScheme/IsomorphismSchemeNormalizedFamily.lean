import Langlands.GroupScheme.OuterIsomorphismProduct

/-! # Isomorphism representatives from uniquely normalized families -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme

namespace LocalGroupIso

variable {S : Scheme.{u}} {G H A : GroupScheme S}
  (a : AutomorphicAction A G) {Q : Over S} (e : LocalGroupIso G H Q)

/-- The family on the product obtained by inverse precomposition in the
acting-group coordinate. -/
def normalizedProductFamily : LocalGroupIso G H (A.X ⊗ Q) :=
  (e.refine (snd A.X Q)).twist a (fst A.X Q)⁻¹

/-- Refining the product family recovers the normalized decomposition. -/
theorem normalizedProductFamily_refine {T : Over S} (p : T ⟶ A.X ⊗ Q) :
    (e.normalizedProductFamily a).refine p =
      (e.refine (p ≫ snd A.X Q)).twist a (p ≫ fst A.X Q)⁻¹ := by
  apply ext_toFun
  intro W t g
  change e.toFun ((t ≫ p) ≫ snd A.X Q)
      (a.act ((t ≫ p) ≫ (fst A.X Q)⁻¹) g) =
    e.toFun (t ≫ (p ≫ snd A.X Q))
      (a.act (t ≫ (p ≫ fst A.X Q)⁻¹) g)
  simp only [Category.assoc, GrpObj.comp_inv]

end LocalGroupIso

namespace GroupIsomorphismScheme

variable {S : Scheme.{u}} {G H A : GroupScheme S}
  (a : AutomorphicAction A G) {Q : Over S} (e : LocalGroupIso G H Q)
  (h : ∀ (T : Over S), Function.Bijective
    (fun z : (T ⟶ A.X) × (T ⟶ Q) => (e.refine z.2).twist a z.1⁻¹))

/-- A natural family and its unique all-test normalized decompositions construct
the full isomorphism representative, without a pre-existing representative. -/
def ofNormalizedFamily : GroupIsomorphismScheme G H where
  parameter := A.X ⊗ Q
  universalIso := e.normalizedProductFamily a
  bijective T := by
    constructor
    · intro p q hpq
      have hz : (p ≫ fst A.X Q, p ≫ snd A.X Q) =
          (q ≫ fst A.X Q, q ≫ snd A.X Q) := by
        apply (h T).1
        simpa only [e.normalizedProductFamily_refine a] using hpq
      apply CartesianMonoidalCategory.hom_ext
      · exact congrArg Prod.fst hz
      · exact congrArg Prod.snd hz
    · intro f
      obtain ⟨⟨d, q⟩, hf⟩ := (h T).2 f
      refine ⟨lift d q, ?_⟩
      simpa only [e.normalizedProductFamily_refine a, lift_fst, lift_snd] using hf

/-- The representative has the stated normalized universal family on every test. -/
theorem ofNormalizedFamily_refine {T : Over S} (p : T ⟶ A.X ⊗ Q) :
    (ofNormalizedFamily a e h).universalIso.refine p =
      (e.refine (p ≫ snd A.X Q)).twist a (p ≫ fst A.X Q)⁻¹ :=
  e.normalizedProductFamily_refine a p

/-- The canonical action on the constructed representative multiplies the
acting-group coordinate. -/
theorem ofNormalizedFamily_equivariant (T : Over S)
    (d x : T ⟶ A.X) (q : T ⟶ Q) :
    lift d (lift x q) ≫ (ofNormalizedFamily a e h).actionHom a =
      lift (d * x) q := by
  let I := ofNormalizedFamily a e h
  apply I.hom_ext
  intro W t g
  change I.universalIso.toFun (t ≫ (lift d (lift x q) ≫ I.actionHom a)) g =
    I.universalIso.toFun (t ≫ lift (d * x) q) g
  simp only [← Category.assoc, comp_lift, I.actionHom_eval]
  change e.toFun ((lift (t ≫ x) (t ≫ q)) ≫ snd A.X Q)
      (a.act ((lift (t ≫ x) (t ≫ q)) ≫ (fst A.X Q)⁻¹)
        (a.act (t ≫ d)⁻¹ g)) =
    e.toFun (lift (t ≫ (d * x)) (t ≫ q) ≫ snd A.X Q)
      (a.act (lift (t ≫ (d * x)) (t ≫ q) ≫ (fst A.X Q)⁻¹) g)
  simp only [GrpObj.comp_inv, lift_fst, lift_snd,
    MonObj.comp_mul, mul_inv_rev, a.act_mul_left]

/-- The normalized-family representative has the label scheme as its exact
outer quotient. -/
def outerOfNormalizedFamily [Flat A.X.hom] [QuasiCompact A.X.hom] :
    OuterIsomorphismScheme (ofNormalizedFamily a e h) a :=
  (ofNormalizedFamily a e h).outerOfProduct a (Iso.refl _) (by
    intro T d x q
    simpa only [Iso.refl_hom, Category.comp_id] using
      ofNormalizedFamily_equivariant a e h T d x q)

@[simp] theorem outerOfNormalizedFamily_parameter
    [Flat A.X.hom] [QuasiCompact A.X.hom] :
    (outerOfNormalizedFamily a e h).parameter = Q := rfl

@[simp] theorem outerOfNormalizedFamily_classMap
    [Flat A.X.hom] [QuasiCompact A.X.hom] :
    (outerOfNormalizedFamily a e h).classMap = snd A.X Q :=
  Category.id_comp _

end GroupIsomorphismScheme

end Langlands.GroupScheme
