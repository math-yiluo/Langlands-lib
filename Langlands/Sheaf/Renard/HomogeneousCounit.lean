import Langlands.Sheaf.Renard.HomogeneousOriginStalk
import Langlands.Sheaf.Renard.HomogeneousSectionStatements
import Langlands.Sheaf.Renard.EquivariantModuleStatements
import Langlands.Sheaf.Renard.HomogeneousEquivalenceStatement

/-!
# The counit of Renard's homogeneous equivalence, from the section comparisons

The literal compact alpha map is a morphism of compatible test actions from
compact sections to the compact induction of the identity-coset stalk. Given the
inverse supplied by the compact alpha/beta comparison and the III.3.1 smooth
equivalence with its exact functors, it yields the counit, hence the III.3.2
equivalence with the exact induction and point-restriction functors.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Langlands.Sheaf.Renard.HomogeneousCounit

open CategoryTheory Opposite
open Langlands.Induction Langlands.Algebra Langlands.HarmonicAnalysis
open Langlands.Sheaf.Equivariant
open Langlands.Sheaf.Renard.SectionActions
open Langlands.Sheaf.Renard.HomogeneousSections
open Langlands.Sheaf.Renard.CompatibleTestActions

attribute [local instance] homogeneousAction

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (hG : Langlands.Topology.IsLocallyProfinite G)
variable (H : Subgroup G) (hH : IsClosed (H : Set G))

/-- The compact-section compatible action of a smooth action sheaf on the homogeneous base. -/
abbrev sectionAction (F : SmoothActionSheaf G (LeftQuotient H)) :=
  (CompactSectionActions.smoothFunctor (quotient_isLocallyProfinite H hG hH)).obj F

/-- The compact induction of the identity-coset stalk, as a smooth compatible action. -/
abbrev inducedStalkAction (F : SmoothActionSheaf G (LeftQuotient H)) :=
  (InductionSheaf.compatibleInduction hG H hH).obj
    (Langlands.SmoothRep.toRep.obj ((pointRestriction H hG hH).obj F))

omit [TopologicalSpace G] [IsTopologicalGroup G] in
theorem smul_origin (g : G) : g⁻¹ • origin H = quotientMap H g := by
  rw [origin, smul_quotientMap, inv_inv, one_mul]

/-- Renard's alpha is linear for the original pointwise tests. -/
theorem alphaCompact_testSmul (F : SmoothActionSheaf G (LeftQuotient H))
    (φ : PointwiseTestAlgebra.Carrier (LeftQuotient H))
    (s : CompactSupport.submodule (CompactSections.ordinary F.obj.obj)) :
    letI := hG.locallyCompactSpace
    alphaCompact H F (CompactSectionTestModule.testSmul (underlying F.obj) φ s) =
      CompactInductionTestModule.multiplier H hH (stalkRepresentation H F.obj) φ.val
        (alphaCompact H F s) := by
  let := hG.locallyCompactSpace
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  funext g
  change (CompactSections.ordinary F.obj.obj).Γgerm (origin H)
      (globalRepresentation F.obj g
        (VectorSheafScalars.smul (underlying F.obj)
          (CompactSectionTestModule.testScalar φ) s.val)) =
    φ.val (quotientMap H g) •
      (CompactSections.ordinary F.obj.obj).Γgerm (origin H)
        (globalRepresentation F.obj g s.val)
  erw [CompactSectionActions.global_germ_transport,
    CompactSectionTestModule.Γgerm_smul (underlying F.obj), map_smul,
    ← CompactSectionActions.global_germ_transport]
  rw [CompactSectionTestModule.testScalar_apply]
  congr 2
  exact smul_origin H g

/-- Renard's alpha as a morphism of the original compatible test actions. -/
def alphaHom (F : SmoothActionSheaf G (LeftQuotient H)) :
    (sectionAction hG H hH F).obj ⟶ (inducedStalkAction hG H hH F).obj where
  moduleHom := ObjectProperty.homMk
    { toAddMonoidHom := (alphaCompact H F).toLinearMap.toAddMonoidHom
      map_smul' := alphaCompact_testSmul hG H hH F }
  comm k s := LinearMap.congr_fun ((alphaCompact H F).isIntertwining' k) s

variable (beta : ∀ F : SmoothActionSheaf G (LeftQuotient H),
  Representation.IntertwiningMap (compactInduced H (stalkRepresentation H F.obj))
    (compactRepresentation F.obj))
variable (hbeta : ∀ F : SmoothActionSheaf G (LeftQuotient H),
  Function.LeftInverse (beta F) (alphaCompact H F) ∧
    Function.RightInverse (beta F) (alphaCompact H F))

include hbeta in
/-- The inverse comparison is linear for the original pointwise tests. -/
theorem beta_testSmul (F : SmoothActionSheaf G (LeftQuotient H))
    (φ : PointwiseTestAlgebra.Carrier (LeftQuotient H))
    (f : CompactFunctions H (stalkRepresentation H F.obj)) :
    letI := hG.locallyCompactSpace
    beta F (CompactInductionTestModule.multiplier H hH (stalkRepresentation H F.obj) φ.val f) =
      CompactSectionTestModule.testSmul (underlying F.obj) φ (beta F f) := by
  apply (hbeta F).1.injective
  rw [alphaCompact_testSmul hG H hH F φ (beta F f), (hbeta F).2, (hbeta F).2]

/-- The inverse comparison as a morphism of the original compatible test actions. -/
def betaHom (F : SmoothActionSheaf G (LeftQuotient H)) :
    (inducedStalkAction hG H hH F).obj ⟶ (sectionAction hG H hH F).obj where
  moduleHom := ObjectProperty.homMk
    { toAddMonoidHom := (beta F).toLinearMap.toAddMonoidHom
      map_smul' := beta_testSmul hG H hH beta hbeta F }
  comm k f := LinearMap.congr_fun ((beta F).isIntertwining' k) f

/-- Renard's alpha is an isomorphism of smooth compatible test actions. -/
def alphaIso (F : SmoothActionSheaf G (LeftQuotient H)) :
    sectionAction hG H hH F ≅ inducedStalkAction hG H hH F where
  hom := ObjectProperty.homMk (alphaHom hG H hH F)
  inv := ObjectProperty.homMk (betaHom hG H hH beta hbeta F)
  hom_inv_id := by
    apply ObjectProperty.hom_ext
    apply CompatibleTestAction.Hom.ext
    apply ObjectProperty.hom_ext
    apply NonUnitalModuleHom.ext
    intro s
    exact (hbeta F).1 s
  inv_hom_id := by
    apply ObjectProperty.hom_ext
    apply CompatibleTestAction.Hom.ext
    apply ObjectProperty.hom_ext
    apply NonUnitalModuleHom.ext
    intro f
    exact (hbeta F).2 f

/-- Naturality of Renard's alpha, as maps of compatible test actions. -/
theorem alphaIso_naturality {F F' : SmoothActionSheaf G (LeftQuotient H)} (u : F ⟶ F') :
    (CompactSectionActions.smoothFunctor (quotient_isLocallyProfinite H hG hH)).map u ≫
        (alphaIso hG H hH beta hbeta F').hom =
      (alphaIso hG H hH beta hbeta F).hom ≫
        (pointRestriction H hG hH ⋙ Langlands.SmoothRep.toRep ⋙
          InductionSheaf.compatibleInduction hG H hH).map u := by
  apply ObjectProperty.hom_ext
  apply CompatibleTestAction.Hom.ext
  apply ObjectProperty.hom_ext
  apply NonUnitalModuleHom.ext
  intro s
  exact (LinearMap.congr_fun
    (congrArg Representation.IntertwiningMap.toLinearMap (alphaCompact_naturality H u)) s).symm

/-- Compact sections are naturally the compact induction of the identity-coset stalk. -/
def alphaNatIso :
    CompactSectionActions.smoothFunctor (quotient_isLocallyProfinite H hG hH) ≅
      pointRestriction H hG hH ⋙ Langlands.SmoothRep.toRep ⋙
        InductionSheaf.compatibleInduction hG H hH :=
  NatIso.ofComponents (alphaIso hG H hH beta hbeta)
    (fun u => alphaIso_naturality hG H hH beta hbeta u)

/-- The counit: induction of the identity-coset stalk recovers every smooth action sheaf. -/
def counitIso
    (e : SmoothActionSheaf G (LeftQuotient H) ≌
      CompactSectionActions.SmoothCompatibleTestAction (G := G) (X := LeftQuotient H))
    (he1 : e.functor = CompactSectionActions.smoothFunctor (quotient_isLocallyProfinite H hG hH))
    (he2 : e.inverse =
      SmoothProjectorActionSheaf.smoothFunctor (quotient_isLocallyProfinite H hG hH) hG) :
    pointRestriction H hG hH ⋙ InductionSheaf.functor hG H hH ≅
      𝟭 (SmoothActionSheaf G (LeftQuotient H)) :=
  Functor.isoWhiskerRight (alphaNatIso hG H hH beta hbeta).symm
      (SmoothProjectorActionSheaf.smoothFunctor (quotient_isLocallyProfinite H hG hH) hG) ≪≫
    (e.unitIso ≪≫ eqToIso (by rw [he1, he2])).symm

end Langlands.Sheaf.Renard.HomogeneousCounit

namespace Langlands.Sheaf.Renard.HomogeneousEquivalence

open CategoryTheory
open Langlands.Sheaf.Renard.HomogeneousSections

attribute [local instance] homogeneousAction

/-- Renard III.3.2, assuming the III.3.1 smooth equivalence and the compact alpha/beta
comparison: induction and original-stalk restriction form an equivalence. -/
theorem statement_of (hS : EquivariantModuleStatements.SmoothStatement.{0})
    (hC : HomogeneousSectionStatements.CompactAlphaBetaStatement) : Statement := by
  intro G _ _ _ _ hG H hH
  obtain ⟨e, he1, he2⟩ := hS G hG (Langlands.Induction.LeftQuotient H)
    (quotient_isLocallyProfinite H hG hH)
  obtain ⟨beta, hbeta, -⟩ := hC G hG H hH
  exact ⟨CategoryTheory.Equivalence.mk (InductionSheaf.functor hG H hH) (pointRestriction H hG hH)
    (HomogeneousOriginStalk.unitIso hG H hH)
    (HomogeneousCounit.counitIso hG H hH beta (fun F => ⟨(hbeta F).1, (hbeta F).2.1⟩)
      e he1 he2), rfl, rfl⟩

end Langlands.Sheaf.Renard.HomogeneousEquivalence
