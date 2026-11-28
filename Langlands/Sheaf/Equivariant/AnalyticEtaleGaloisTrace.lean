import Langlands.Cohomology.AnalyticGaloisSiteCover
import Langlands.Geometry.Analytic.EtaleCoverGluing
import Langlands.Sheaf.Equivariant.TwistedGlobalSections
import Mathlib.RepresentationTheory.Invariants

/-! # Descent and trace on sections of an analytic étale Galois cover -/

noncomputable section

universe u v w z

namespace Langlands.Analytic.SaturatedAtlasPresentation.AnalyticGaloisCover

open _root_.CategoryTheory Opposite
open Langlands.Cohomology (GaloisCovering)
open Langlands.Sheaf.Equivariant.TwistedOver (sheafSectionsModule)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {Y X : LocalizedCategory.{u, v, v} (K := K)} {p : Y ⟶ X}
  {G : Type z} [Group G] (c : AnalyticGaloisCover G p)

/-- The covering arrow as an object of the small étale site of the base. -/
abbrev coverTest : EtaleSite X := MorphismProperty.Over.mk ⊤ p c.etale_map

/-- The map from the covering test to the identity test. -/
def coverToSelf : c.coverTest ⟶ etaleSiteTop X :=
  MorphismProperty.Over.homMk p (Category.comp_id _)

private def siteCover : GaloisCovering (etaleTopology X) G c.coverTest (etaleSiteTop X) :=
  c.toEtaleSiteCover c.coverToSelf

/-- A deck automorphism acts on the covering test over the base. -/
abbrev deckTest (g : G) : c.coverTest ⟶ c.coverTest := (siteCover c).deck g

variable {R : Type (max u (v + 1) w)} [CommRing R]
  (F : Sheaf (etaleTopology X) (ModuleCat.{max u (v + 1) w} R))

/-- Restriction to the covering test is injective for every module sheaf. -/
theorem coverRestriction_injective : Function.Injective (F.obj.map c.coverToSelf.op) :=
  (siteCover c).map_p_injective F

/-- An invariant section on the covering object descends uniquely to the base test. -/
theorem existsUnique_of_deckInvariant (s : F.obj.obj (op c.coverTest))
    (hs : ∀ g : G, F.obj.map (c.deckTest g).op s = s) :
    ∃! a : F.obj.obj (op (etaleSiteTop X)), F.obj.map c.coverToSelf.op a = s := by
  obtain ⟨a, ha⟩ := (siteCover c).exists_map_p_eq F s hs
  exact ⟨a, ha, fun b hb => c.coverRestriction_injective F (hb.trans ha.symm)⟩

/-- The deck representation on sections over the covering object is pullback along the
inverse deck automorphism. -/
def deckSectionRepresentation : Representation R G (F.obj.obj (op c.coverTest)) where
  toFun g := (F.obj.map (c.deckTest g⁻¹).op).hom
  map_one' := by
    simp only [deckTest, inv_one, (siteCover c).deck_one, op_id, F.obj.map_id]
    rfl
  map_mul' g h := by
    simp only [deckTest, mul_inv_rev, (siteCover c).deck_mul, op_comp, F.obj.map_comp]
    rfl

private theorem invariant_iff (s : F.obj.obj (op c.coverTest)) :
    s ∈ (c.deckSectionRepresentation F).invariants ↔
      ∀ g : G, F.obj.map (c.deckTest g).op s = s := by
  change (∀ g : G, F.obj.map (c.deckTest g⁻¹).op s = s) ↔ _
  constructor
  · intro h g
    simpa only [inv_inv] using h g⁻¹
  · intro h g
    exact h g⁻¹

/-- Sections over the base identify by restriction with the invariant sections on the cover. -/
def deckInvariantSectionsEquiv :
    (F.obj.obj (op (etaleSiteTop X))) ≃ₗ[R] (c.deckSectionRepresentation F).invariants :=
  LinearEquiv.ofBijective ((F.obj.map c.coverToSelf.op).hom.codRestrict
    (c.deckSectionRepresentation F).invariants
    (fun a g => by
      change F.obj.map (c.deckTest g⁻¹).op (F.obj.map c.coverToSelf.op a) =
        F.obj.map c.coverToSelf.op a
      rw [GaloisCovering.map_map_apply]
      exact congrArg (fun k => F.obj.map k.op a) ((siteCover c).deck_comp g⁻¹)))
    ⟨fun _ _ h => coverRestriction_injective c F (congrArg Subtype.val h), fun b => by
      obtain ⟨a, ha, _⟩ := c.existsUnique_of_deckInvariant F b.val
        ((invariant_iff c F b.val).mp b.property)
      exact ⟨a, Subtype.ext ha⟩⟩

variable [Fintype G]

/-- Trace on global sections of pulled-back coefficients. It descends the unnormalized
deck norm along the original surjective étale cover. -/
def traceSections :
    F.obj.obj (op c.coverTest) →ₗ[R] F.obj.obj (op (etaleSiteTop X)) :=
  (c.deckInvariantSectionsEquiv F).symm.toLinearMap.comp <|
    (c.deckSectionRepresentation F).norm.codRestrict _
      (fun s g => (c.deckSectionRepresentation F).self_norm_apply g s)

/-- Restriction of a trace is the finite deck sum. -/
theorem restrict_traceSections (s : F.obj.obj (op c.coverTest)) :
    F.obj.map c.coverToSelf.op (c.traceSections F s) =
      ∑ g : G, F.obj.map (c.deckTest g).op s := by
  have h : F.obj.map c.coverToSelf.op (c.traceSections F s) =
      (c.deckSectionRepresentation F).norm s :=
    congrArg Subtype.val ((c.deckInvariantSectionsEquiv F).apply_symm_apply
      ⟨_, fun g => (c.deckSectionRepresentation F).self_norm_apply g s⟩)
  rw [h, Representation.norm, LinearMap.sum_apply]
  exact Equiv.sum_comp (Equiv.inv G) (fun g => F.obj.map (c.deckTest g).op s)

/-- Trace of a restriction multiplies the original section by the order of the deck group. -/
theorem traceSections_restrict (a : F.obj.obj (op (etaleSiteTop X))) :
    c.traceSections F (F.obj.map c.coverToSelf.op a) = Fintype.card G • a := by
  apply c.coverRestriction_injective F
  rw [c.restrict_traceSections, map_nsmul]
  have h (g : G) : F.obj.map (c.deckTest g).op (F.obj.map c.coverToSelf.op a) =
      F.obj.map c.coverToSelf.op a :=
    (invariant_iff c F _).mp ((c.deckInvariantSectionsEquiv F) a).property g
  simp only [h, Finset.sum_const, Finset.card_univ]

/-- Trace on sections is natural in the sheaf on the base. -/
theorem traceSections_naturality
    {F' : Sheaf (etaleTopology X) (ModuleCat.{max u (v + 1) w} R)} (f : F ⟶ F')
    (s : F.obj.obj (op c.coverTest)) :
    f.hom.app (op (etaleSiteTop X)) (c.traceSections F s) =
      c.traceSections F' (f.hom.app (op c.coverTest) s) := by
  apply c.coverRestriction_injective F'
  rw [← ModuleCat.comp_apply, ← f.hom.naturality, ModuleCat.comp_apply,
    c.restrict_traceSections, c.restrict_traceSections, map_sum]
  apply Finset.sum_congr rfl
  intro g _
  exact ConcreteCategory.congr_hom (f.hom.naturality (c.deckTest g).op) s

/-- The trace as a natural transformation of evaluation functors on the base site. -/
def traceSectionsNatTrans :
    sheafSectionsModule (etaleTopology X) R c.coverTest ⟶
      sheafSectionsModule (etaleTopology X) R (etaleSiteTop X) where
  app F := ModuleCat.ofHom (c.traceSections F)
  naturality _ _ f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro s
    exact (c.traceSections_naturality _ f s).symm

end Langlands.Analytic.SaturatedAtlasPresentation.AnalyticGaloisCover
