import Langlands.Sheaf.Equivariant.TwistedCompactSupport
import Langlands.Sheaf.Equivariant.TwistedGodement
import Langlands.Representation.Category.ExactInclusion
import Langlands.Cohomology.ExactBaseChange
import Langlands.Cohomology.DivisibleSystem.PermutationProjective

/-!
# Comparison maps for equivariant compactly supported cohomology

On a twisted site with a family of points compatible with the group action, the
compactly supported cohomology of a discrete sheaf, as smooth representations of
`G`, maps to the compactly supported cohomology of the underlying sheaf on the site
over `X`. The invariant compactly supported global sections are left exact; their
right derived functors receive an edge map to the invariants of the smooth
compactly supported cohomology.
-/

noncomputable section

namespace Langlands.Sheaf.Equivariant.TwistedOver

open CategoryTheory CategoryTheory.Limits
open Langlands.Sheaf.PointSupport Langlands.Cohomology

universe w v u uG uI

section SmoothFunctors

variable (R : Type w) [CommRing R] (G : Type uG) [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G]

/-- The module underlying a smooth representation. -/
abbrev smoothForget : SmoothRep.{w, uG, w} R G ⥤ ModuleCat.{w} R :=
  SmoothRep.toRep ⋙ forget₂ (Rep.{w} R G) (ModuleCat.{w} R)

instance smoothForget_preservesFiniteLimits : PreservesFiniteLimits (smoothForget R G) :=
  comp_preservesFiniteLimits _ _

instance smoothForget_preservesFiniteColimits : PreservesFiniteColimits (smoothForget R G) :=
  comp_preservesFiniteColimits _ _

/-- The `G`-invariants of smooth representations are left exact: Mathlib's invariants
functor is a right adjoint. -/
instance smoothInvariantsFunctor_preservesFiniteLimits :
    PreservesFiniteLimits (smoothInvariantsFunctor.{w, uG, w} R G) := by
  have := (Rep.invariantsAdjunction R G).rightAdjoint_preservesLimits
  exact comp_preservesFiniteLimits _ _

/-- A `G`-invariant vector of a representation is smooth: it is fixed by the open
subgroup `G`. So the invariants of the smooth part are the invariants. -/
def smoothPartInvariantsIso :
    SmoothRep.smoothPartFunctor R G ⋙ smoothInvariantsFunctor.{w, uG, w} R G ≅
      Rep.invariantsFunctor R G :=
  NatIso.ofComponents
    (fun _ => LinearEquiv.toModuleIso
      { toFun := fun v => ⟨v.1.1, fun g => congrArg Subtype.val (v.2 g)⟩
        invFun := fun v => ⟨⟨v.1, ⟨⊤, fun g => v.2 g⟩⟩, fun g => Subtype.ext (v.2 g)⟩
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl })
    (fun _ => rfl)

end SmoothFunctors

variable {C : Type u} [Category.{v} C] {P : MorphismProperty C} [P.RespectsIso] {X : C}
variable {G : Type uG} [Group G] {ρ : G →* Aut X}
variable {J : GrothendieckTopology (P.Over ⊤ X)}
variable {I : Type uI} [MulAction G I] {Φ : I → J.Point.{w}}

variable [P.ContainsIdentities]
variable {R : Type w} [CommRing R]
variable [LocallySmall.{w} (P.Over ⊤ X)]
variable [TopologicalSpace I] [ContinuousConstSMul G I]
variable (J) [IsTranslationInvariant (ρ := ρ) J]
variable [TopologicalSpace G] [IsTopologicalGroup G]
variable (L : LocalActionSystem (TwistedOver P ρ) G)

section Inclusion

variable (R) in
/-- The inclusion of the smooth compactly supported global sections of a discrete
sheaf into the compactly supported sections of its restriction to the site over
`X`: the counit of the smooth-part adjunction. -/
def smoothCompactInclusion (E : PointEquivariance ρ Φ) :
    discreteCompactSections J R L E ⋙ smoothForget R G ⟶
      (L.discreteSheafInclusion (ModuleCat.{w} R) (twistedTopology ρ J) ⋙
        restriction ρ J (ModuleCat.{w} R)) ⋙ sheafCompactSections J Φ R (base P ρ).obj where
  app F := (forget₂ (Rep.{w} R G) (ModuleCat.{w} R)).map
    ((SmoothRep.toRepSmoothPartAdjunction R G).counit.app
      ((sheafCompactSectionsRep J R E).obj F.obj))
  naturality F F' f := by
    have h := (SmoothRep.toRepSmoothPartAdjunction R G).counit.naturality
      ((sheafCompactSectionsRep J R E).map f.hom)
    exact ((forget₂ (Rep.{w} R G) (ModuleCat.{w} R)).map_comp _ _).symm.trans
      (((forget₂ (Rep.{w} R G) (ModuleCat.{w} R)).congr_map h).trans
        ((forget₂ (Rep.{w} R G) (ModuleCat.{w} R)).map_comp _ _))

theorem smoothCompactInclusion_app_apply (E : PointEquivariance ρ Φ)
    (F : L.DiscreteSheaf (ModuleCat.{w} R) (twistedTopology ρ J))
    (s : ((discreteCompactSections J R L E ⋙ smoothForget R G).obj F)) :
    ((smoothCompactInclusion J R L E).app F).hom s = s.1 := rfl

end Inclusion

variable [HasSheafify J (ModuleCat.{w} R)]
variable [HasSheafify (twistedTopology ρ J) (ModuleCat.{w} R)]
variable [L.HasFiniteEquivariantRefinements (twistedTopology ρ J)]

section Invariants

variable (R) in
/-- Invariant compactly supported global sections of discrete sheaves: the
`G`-invariant vectors of the smooth compactly supported global sections. -/
def discreteInvariantCompactSections (E : PointEquivariance ρ Φ) :
    L.DiscreteSheaf (ModuleCat.{w} R) (twistedTopology ρ J) ⥤ ModuleCat.{w} R :=
  discreteCompactSections J R L E ⋙ smoothInvariantsFunctor R G

instance discreteInvariantCompactSections_additive (E : PointEquivariance ρ Φ) :
    (discreteInvariantCompactSections J R L E).Additive :=
  inferInstanceAs (discreteCompactSections J R L E ⋙ smoothInvariantsFunctor R G).Additive

instance discreteInvariantCompactSections_preservesFiniteLimits (E : PointEquivariance ρ Φ) :
    PreservesFiniteLimits (discreteInvariantCompactSections J R L E) :=
  comp_preservesFiniteLimits _ _

/-- The invariant compactly supported global sections are the `G`-invariant
compactly supported global sections of the sheaf. -/
def discreteInvariantCompactSectionsIso (E : PointEquivariance ρ Φ) :
    discreteInvariantCompactSections J R L E ≅
      L.discreteSheafInclusion (ModuleCat.{w} R) (twistedTopology ρ J) ⋙
        sheafCompactSectionsRep J R E ⋙ Rep.invariantsFunctor R G :=
  Functor.isoWhiskerLeft
    (L.discreteSheafInclusion (ModuleCat.{w} R) (twistedTopology ρ J) ⋙
      sheafCompactSectionsRep J R E) (smoothPartInvariantsIso R G)

variable [EnoughInjectives (Sheaf (twistedTopology ρ J) (ModuleCat.{w} R))]

variable (R) in
/-- Degree `q` invariant compactly supported cohomology of discrete sheaves: the
right derived functors of the invariant compactly supported global sections,
computed with injective resolutions among discrete sheaves. -/
def discreteInvariantCompactDerived (E : PointEquivariance ρ Φ) (q : ℕ) :
    L.DiscreteSheaf (ModuleCat.{w} R) (twistedTopology ρ J) ⥤ ModuleCat.{w} R :=
  (discreteInvariantCompactSections J R L E).rightDerived q

/-- In degree zero, the derived functor is the functor itself. -/
def discreteInvariantCompactDerivedZeroIso (E : PointEquivariance ρ Φ) :
    discreteInvariantCompactDerived J R L E 0 ≅ discreteInvariantCompactSections J R L E :=
  (discreteInvariantCompactSections J R L E).rightDerivedZeroIsoSelf

variable (R) in
/-- The edge map from invariant compactly supported cohomology to the invariants of
the smooth compactly supported cohomology. -/
def invariantEdgeMap (E : PointEquivariance ρ Φ) (q : ℕ) :
    discreteInvariantCompactDerived J R L E q ⟶
      discreteCompactDerived J R L E q ⋙ smoothInvariantsFunctor R G :=
  LeftExactHomology.derivedNatTrans (smoothInvariantsFunctor R G)
    (discreteCompactSections J R L E) q

/-- In degree zero, the edge map is an isomorphism. -/
instance isIso_invariantEdgeMap_zero (E : PointEquivariance ρ Φ) :
    IsIso (invariantEdgeMap J R L E 0) :=
  LeftExactHomology.isIso_derivedNatTrans_zero _ _

end Invariants

section Comparison

/-- Restriction to the site over `X` is additive: it acts on morphisms of sheaves
by whiskering. -/
instance restriction_additive : (restriction ρ J (ModuleCat.{w} R)).Additive where
  map_add := rfl

variable [∀ F : (P.Over ⊤ X)ᵒᵖ ⥤ ModuleCat.{w} R, (ι P ρ).op.HasPointwiseRightKanExtension F]

/-- Restriction to the site over `X` is a left adjoint, so it preserves colimits. -/
instance restriction_preservesFiniteColimits :
    PreservesFiniteColimits (restriction ρ J (ModuleCat.{w} R)) := by
  have := (restrictionAdjunction ρ J (ModuleCat.{w} R)).leftAdjoint_preservesColimits.{0, 0}
  exact PreservesColimitsOfSize.preservesFiniteColimits _

/-- Restricting a discrete sheaf to the site over `X` is exact. -/
instance discreteRestriction_preservesFiniteLimits :
    PreservesFiniteLimits (L.discreteSheafInclusion (ModuleCat.{w} R) (twistedTopology ρ J) ⋙
      restriction ρ J (ModuleCat.{w} R)) :=
  comp_preservesFiniteLimits _ _

instance discreteRestriction_preservesFiniteColimits :
    PreservesFiniteColimits (L.discreteSheafInclusion (ModuleCat.{w} R) (twistedTopology ρ J) ⋙
      restriction ρ J (ModuleCat.{w} R)) :=
  comp_preservesFiniteColimits _ _

variable [EnoughInjectives (Sheaf (twistedTopology ρ J) (ModuleCat.{w} R))]
variable [EnoughInjectives (Sheaf J (ModuleCat.{w} R))]

variable (R) in
/-- The comparison from the smooth compactly supported cohomology of a discrete
sheaf on the twisted site to the compactly supported cohomology of its restriction
to the site over `X`, in degree `q`: the base change transformation of the
inclusion `smoothCompactInclusion` along the exact functors `smoothForget` and
restriction. This is the shape of Berkovich's maps
`H^q_c(X{G}, F) → H^q_c(X, b^*F)`. -/
def compactComparison (E : PointEquivariance ρ Φ) (q : ℕ) :
    discreteCompactDerived J R L E q ⋙ smoothForget R G ⟶
      (L.discreteSheafInclusion (ModuleCat.{w} R) (twistedTopology ρ J) ⋙
        restriction ρ J (ModuleCat.{w} R)) ⋙ compactDerived J Φ R (base P ρ).obj q :=
  ExactBaseChange.baseChangeNatTrans (smoothCompactInclusion J R L E) q

end Comparison

end Langlands.Sheaf.Equivariant.TwistedOver
