import Langlands.Sheaf.Equivariant.TwistedCompactComparison
import Langlands.Sheaf.Equivariant.TwistedInductionUnderlyingMaps
import Langlands.Sheaf.PointProductSetSections
import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono

/-! # Exactness of the discrete Godement functor on a twisted site -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxHeartbeats 60000

namespace Langlands.Sheaf.Equivariant.TwistedOver

open CategoryTheory CategoryTheory.Limits Opposite LocalActionSystem

universe u v uG w

variable {C : Type u} [Category.{v} C] {P : MorphismProperty C} [P.RespectsIso]
variable {X : C} {G : Type uG} [Group G] [TopologicalSpace G] (ρ : G →* Aut X)
variable (J : GrothendieckTopology (P.Over ⊤ X)) [IsTranslationInvariant (ρ := ρ) J]
variable (L : LocalActionSystem (TwistedOver P ρ) G)
variable [L.HasFiniteEquivariantRefinements (twistedTopology ρ J)]
variable {I : Type w} (points : I → J.Point.{w})
variable (R : Type w) [CommRing R]

private theorem map_discreteSubmodule_underlying {T : Type u} [Category.{v} T]
    (S : LocalActionSystem T G) {F F' : Tᵒᵖ ⥤ ModuleCat.{w} R}
    (η : F ⋙ forget (ModuleCat R) ⟶ F' ⋙ forget (ModuleCat R))
    {U : T} {s : F.obj (op U)} (hs : s ∈ discreteSubmodule S F U) :
    η.app (op U) s ∈ discreteSubmodule S F' U := by
  intro V H a ha g
  have hfix : IsDiscreteSection (F ⋙ forget (ModuleCat R)) a
      ((F ⋙ forget (ModuleCat R)).map g.op s) := hs V H a ha g
  exact (η.naturality_apply g.op s) ▸ hfix.map η

private theorem discreteCoreflector_map_app_surjective_of_setSection
    {F F' : Sheaf (twistedTopology ρ J) (ModuleCat.{w} R)} (φ : F ⟶ F')
    (η : F'.obj ⋙ forget (ModuleCat R) ⟶ F.obj ⋙ forget (ModuleCat R))
    (hη : η ≫ Functor.whiskerRight φ.hom (forget (ModuleCat R)) = 𝟙 _)
    (U : (TwistedOver P ρ)ᵒᵖ) :
    Function.Surjective (((discreteCoreflector L (twistedTopology ρ J)).map φ).hom.hom.app U) := by
  intro s
  change discreteSubmodule L F'.obj U.unop at s
  have hs := map_discreteSubmodule_underlying R L η s.property
  refine ⟨⟨η.app U s.val, hs⟩, Subtype.ext ?_⟩
  change φ.hom.app U (η.app U s.val) = s.val
  have h := ConcreteCategory.congr_hom (NatTrans.congr_app hη U)
    (show (F'.obj ⋙ forget (ModuleCat R)).obj U from s.val)
  exact h

variable [∀ F : (P.Over ⊤ X)ᵒᵖ ⥤ ModuleCat.{w} R,
  (ι P ρ).op.HasPointwiseRightKanExtension F]

/-- The product of skyscrapers with independent coefficients, induced to the twisted
site and taken into the discrete subcategory. -/
def discretePointProductFunctor :
    (I → ModuleCat.{w} R) ⥤ L.DiscreteSheaf (ModuleCat.{w} R) (twistedTopology ρ J) :=
  PointProduct.productFunctor points (ModuleCat R) ⋙ induction ρ J (ModuleCat R) ⋙
    discreteCoreflector L (twistedTopology ρ J)

set_option maxHeartbeats 400000 in
/-- A coefficientwise surjection lifts every section of the actual discrete point
product. A set section on the ordinary point product induces a natural set section
on the twisted site, which preserves each open-subgroup fixedness condition. -/
theorem discretePointProductFunctor_map_app_surjective {M N : I → ModuleCat.{w} R}
    (f : M ⟶ N) (hf : ∀ i, Function.Surjective (f i)) (U : (TwistedOver P ρ)ᵒᵖ) :
    Function.Surjective (((discretePointProductFunctor ρ J L points R).map f).hom.hom.app U) := by
  let A := ModuleCat.{w} R
  let F := PointProduct.productFunctor points A
  let φ : F.obj M ⟶ F.obj N := F.map f
  let τ : (F.obj N).obj ⋙ forget A ⟶ (F.obj M).obj ⋙ forget A :=
    PointProduct.setSection points f hf
  have hτ : τ ≫ Functor.whiskerRight φ.hom (forget A) = 𝟙 _ := by
    ext V s
    exact PointProduct.productFunctor_map_setSection points f hf V s
  have hσ := InductionCoordinates.inductionUnderlyingMap_rightInverse ρ _ τ hτ
  rw [InductionCoordinates.inductionUnderlyingMap_whiskerRight] at hσ
  exact discreteCoreflector_map_app_surjective_of_setSection ρ J L R
    ((induction ρ J A).map φ) (InductionCoordinates.inductionUnderlyingMap ρ τ) hσ U

variable [HasSheafify J (ModuleCat.{w} R)]
  [HasSheafify (twistedTopology ρ J) (ModuleCat.{w} R)]

/-- The existing discrete Godement functor is the discrete point product of the
site fibers of the underlying ordinary sheaf. -/
def discreteGodementPointProductIso :
    discreteZeroFunctor ρ J L points R ≅
      L.discreteSheafInclusion (ModuleCat R) (twistedTopology ρ J) ⋙
        restriction ρ J (ModuleCat R) ⋙ PointProduct.fiberFunctor points (ModuleCat R) ⋙
          discretePointProductFunctor ρ J L points R :=
  Functor.isoWhiskerLeft
    (L.discreteSheafInclusion (ModuleCat R) (twistedTopology ρ J) ⋙ restriction ρ J (ModuleCat R))
    (Functor.isoWhiskerRight (PointProduct.godementZeroIso points (ModuleCat R))
      (induction ρ J (ModuleCat R) ⋙ discreteCoreflector L (twistedTopology ρ J)))

instance discretePointProductFunctor_preservesEpimorphisms :
    (discretePointProductFunctor ρ J L points R).PreservesEpimorphisms where
  preserves f _ := by
    apply (L.discreteSheafInclusion (ModuleCat R) (twistedTopology ρ J) ⋙
      sheafToPresheaf (twistedTopology ρ J) (ModuleCat R)).epi_of_epi_map
    change Epi (((discretePointProductFunctor ρ J L points R).map f).hom.hom)
    have h (i : I) : Epi (f i) := by
      change Epi (((piEquivalenceFunctorDiscrete I (ModuleCat.{w} R)).functor.map f).app ⟨i⟩)
      infer_instance
    have : ∀ U, Epi (((discretePointProductFunctor ρ J L points R).map f).hom.hom.app U) :=
      fun U => (ModuleCat.epi_iff_surjective _).mpr <|
        discretePointProductFunctor_map_app_surjective ρ J L points R f
          (fun i => (ModuleCat.epi_iff_surjective (f i)).mp (h i)) U
    exact NatTrans.epi_of_epi_app _

/-- The degree-zero discrete Godement functor preserves epimorphisms. -/
instance discreteZeroFunctor_preservesEpimorphisms :
    (discreteZeroFunctor ρ J L points R).PreservesEpimorphisms := by
  let e := (piEquivalenceFunctorDiscrete I (ModuleCat.{w} R)).functor
  let F := PointProduct.fiberFunctor points (ModuleCat.{w} R)
  have : (F ⋙ e).PreservesEpimorphisms := ⟨fun f _ => by
    have : ∀ i, Epi (((F ⋙ e).map f).app i) := fun i =>
      inferInstanceAs (Epi ((points i.as).sheafFiber.map f))
    exact NatTrans.epi_of_epi_app _⟩
  have : F.PreservesEpimorphisms := Functor.preservesEpimorphisms_of_preserves_of_reflects F e
  exact Functor.PreservesEpimorphisms.of_iso (discreteGodementPointProductIso ρ J L points R).symm

variable [LocallySmall.{w} (P.Over ⊤ X)]

/-- The degree-zero discrete Godement functor preserves finite limits. -/
instance discreteZeroFunctor_preservesFiniteLimits :
    PreservesFiniteLimits (discreteZeroFunctor ρ J L points R) := by
  have : (discreteCoreflector (R := R) L (twistedTopology ρ J)).IsRightAdjoint :=
    (discreteAdjunction (R := R) L (twistedTopology ρ J)).isRightAdjoint
  let e := (piEquivalenceFunctorDiscrete I (ModuleCat.{w} R)).functor
  let F := PointProduct.fiberFunctor points (ModuleCat.{w} R)
  have : PreservesFiniteLimits (F ⋙ e) := preservesFiniteLimits_of_evaluation _ fun i =>
    inferInstanceAs (PreservesFiniteLimits ((points i.as).sheafFiber (A := ModuleCat.{w} R)))
  have : PreservesFiniteLimits F := preservesFiniteLimits_of_reflects_of_preserves F e
  have : PreservesFiniteLimits (discretePointProductFunctor ρ J L points R) := by
    dsimp only [discretePointProductFunctor]
    infer_instance
  exact preservesFiniteLimits_of_natIso (discreteGodementPointProductIso ρ J L points R).symm

instance discreteZeroFunctor_additive :
    (discreteZeroFunctor ρ J L points R).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- The degree-zero discrete Godement functor is exact. -/
instance discreteZeroFunctor_preservesHomology :
    (discreteZeroFunctor ρ J L points R).PreservesHomology :=
  Functor.preservesHomology_of_preservesEpis_and_kernels _

/-- The degree-zero discrete Godement functor preserves finite colimits. -/
instance discreteZeroFunctor_preservesFiniteColimits :
    PreservesFiniteColimits (discreteZeroFunctor ρ J L points R) :=
  Functor.preservesFiniteColimits_of_preservesHomology _

end Langlands.Sheaf.Equivariant.TwistedOver
