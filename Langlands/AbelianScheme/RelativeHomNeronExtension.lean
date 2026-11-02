import Langlands.AbelianScheme.RelativeEndomorphismRepresentabilityOfPieces
import Langlands.AnthropicFLT.Theorems.Thm_NeronModelInfra_NeronModelPropertyBundle_of_abelianSchemePropertyBundle
import Langlands.AnthropicFLT.Theorems.Thm_NeronModelInfra_genericFibreRestrict_injective_of_flat_of_isSeparated
import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativeGroupLawGrpObj

/-! # Extension of homomorphisms of abelian schemes over discrete valuation rings -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonObj
open AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj CategoryTheory.Obj
attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory
  CategoryTheory.Over.braidedCategory

namespace Langlands.AbelianScheme

universe u

section Monoidal

variable {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]
  (F : C ⥤ D) [F.Monoidal]

/-- A morphism of monoid objects is a monoid morphism if its image under a monoidal functor is,
provided that the functor is injective on morphisms from `𝟙_ C` and from `M ⊗ M` to `N`. -/
theorem isMonHom_of_map {M N : C} [MonObj M] [MonObj N] (f : M ⟶ N) [IsMonHom (F.map f)]
    (h₀ : ∀ g g' : 𝟙_ C ⟶ N, F.map g = F.map g' → g = g')
    (h₂ : ∀ g g' : M ⊗ M ⟶ N, F.map g = F.map g' → g = g') : IsMonHom f where
  one_hom := h₀ _ _ <| by
    simp [← Functor.obj.η_def_assoc, ← Functor.obj.η_def,
      ← cancel_epi (Functor.LaxMonoidal.ε F)]
  mul_hom := h₂ _ _ <| by
    simp [← Functor.obj.μ_def_assoc, ← Functor.obj.μ_def, ← Functor.LaxMonoidal.μ_natural_assoc,
      ← cancel_epi (Functor.LaxMonoidal.μ F ..)]

end Monoidal

section GenericFibre

variable {V : Type u} [CommRing V] [IsDomain V] (K : Type u) [Field K] [Algebra V K]
  [IsFractionRing V K]

/-- Over the spectrum of a domain, base change to the generic fibre is injective on morphisms
from a flat scheme to a separated scheme. -/
theorem genericFibre_map_injective {Y Z : Over (Spec (CommRingCat.of V))} [Flat Y.hom]
    [IsSeparated Z.hom] {g g' : Y ⟶ Z}
    (h : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap V K)))).map g =
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap V K)))).map g') : g = g' := by
  have h1 : pullback.fst Y.hom (Spec.map (CommRingCat.ofHom (algebraMap V K))) ≫ g.left =
      pullback.fst Y.hom (Spec.map (CommRingCat.ofHom (algebraMap V K))) ≫ g'.left := by
    have := congrArg (fun w => w.left ≫ pullback.fst Z.hom
      (Spec.map (CommRingCat.ofHom (algebraMap V K)))) h
    simpa using this
  have hinj := NeronModelInfra.genericFibreRestrict_injective_of_flat_of_isSeparated V K Z.hom Y.hom
  have h2 := hinj (a₁ := ⟨g.left, Over.w g⟩) (a₂ := ⟨g'.left, Over.w g'⟩) (by
    apply Subtype.ext
    apply pullback.hom_ext
    · simpa [NeronModelInfra.genericFibreRestrict] using h1
    · simp [NeronModelInfra.genericFibreRestrict])
  exact Over.OverMorphism.ext (congrArg Subtype.val h2)

variable [IsDiscreteValuationRing V]

/-- Over a discrete valuation ring `V` with fraction field `K`, every homomorphism of the generic
fibres of group schemes `G` and `H` is the base change of a homomorphism `G ⟶ H`, if `G` is
smooth and `H` satisfies FLT's abelian scheme property bundle. -/
theorem baseChange_map_surjective (G H : Grp (Over (Spec (CommRingCat.of V))))
    [Smooth G.X.hom] (hH : GoodReductionJacobian.AbelianSchemePropertyBundle V H.X.hom) :
    Function.Surjective
      ((GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap V K)))).map :
        (G ⟶ H) → _) := by
  intro ψ
  have hN := NeronModelInfra.NeronModelPropertyBundle.of_abelianSchemePropertyBundle V K hH
  have : IsProper H.X.hom := hH.proper
  let v : NeronModelInfra.SchemeHomOver
      (pullback.snd G.X.hom (NeronModelInfra.specGenericFibreInclusion V K))
      (pullback.snd H.X.hom (NeronModelInfra.specGenericFibreInclusion V K)) :=
    ⟨ψ.hom.hom.left, Over.w ψ.hom.hom⟩
  obtain ⟨φ, hφ⟩ := (hN.neronMapping G.X.left G.X.hom inferInstance).2 v
  let φ' : G.X ⟶ H.X := Over.homMk φ.1 φ.2
  have hmap : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap V K)))).map φ' =
      ψ.hom.hom := by
    apply Over.OverMorphism.ext
    have h1 : (NeronModelInfra.genericFibreRestrict V K H.X.hom G.X.hom φ).1 = ψ.hom.hom.left :=
      congrArg Subtype.val hφ
    rw [← h1]
    apply pullback.hom_ext
    · simp [NeronModelInfra.genericFibreRestrict, φ']
    · simp [NeronModelInfra.genericFibreRestrict, φ']
  have : IsMonHom ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap V K)))).map φ') := by
    rw [hmap]; infer_instance
  have hflat₀ : Flat (𝟙_ (Over (Spec (CommRingCat.of V)))).hom := by
    rw [Over.tensorUnit_hom]; exact MorphismProperty.id_mem @Flat _
  have hflat₂ : Flat (G.X ⊗ G.X).hom := by
    rw [Over.tensorObj_hom]; infer_instance
  have : IsMonHom φ' :=
    isMonHom_of_map (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap V K)))) φ'
      (fun _ _ h => genericFibre_map_injective K h) (fun _ _ h => genericFibre_map_injective K h)
  refine ⟨Grp.homMk φ', ?_⟩
  apply Grp.hom_ext
  exact hmap

end GenericFibre

/-- The base change of an abelian scheme to the spectrum of a ring `V` satisfies FLT's abelian
scheme property bundle. -/
theorem abelianSchemePropertyBundle_baseChange {V : Type u} [CommRing V] {S : Scheme.{u}}
    (B : Langlands.AbelianScheme S) (t : Spec (CommRingCat.of V) ⟶ S) :
    GoodReductionJacobian.AbelianSchemePropertyBundle V
      ((CommGroupScheme.baseChange t).obj B.toCommGroupScheme).X.hom where
  smooth := by change Smooth (pullback.snd B.X.hom t); infer_instance
  proper := by change IsProper (pullback.snd B.X.hom t); infer_instance
  connectedFibres := fun s => by
    change _root_.IsConnected ((pullback.snd B.X.hom t).base ⁻¹' {s})
    exact (pullback.snd B.X.hom t).isConnected_preimage_singleton s
  hasGroupLaw := ⟨@GoodReductionJacobian.relativeGroupLawOfGrpObj V _ _ _
    (inferInstanceAs (GrpObj ((CommGroupScheme.baseChange t).obj B.toCommGroupScheme).X))⟩

/-- **Extension of homomorphisms of abelian schemes over a discrete valuation ring.** For abelian
schemes `A` and `B` over `S` and a discrete valuation ring `V` over `S` with fraction field `K`,
every homomorphism `A_K ⟶ B_K` is the restriction of a homomorphism `A_V ⟶ B_V`. -/
theorem neronHomExtension : NeronHomExtension.{u} := by
  intro S A B V _ _ _ K _ _ _ t χK
  let a : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap V K)) ≫ t) ⟶ Over.mk t :=
    Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap V K))) rfl
  let ψ := (Langlands.GroupScheme.Cartier.baseChangeCompIso A.toCommGroupScheme a).inv ≫
    CommGroupScheme.groupHom χK ≫
      (Langlands.GroupScheme.Cartier.baseChangeCompIso B.toCommGroupScheme a).hom
  have : Smooth (Langlands.GroupScheme.Cartier.testBaseChange (Over.mk t)
      A.toCommGroupScheme).X.hom := by
    change Smooth (pullback.snd A.X.hom t); infer_instance
  obtain ⟨χ₀, hχ₀⟩ := baseChange_map_surjective K _ _
    (abelianSchemePropertyBundle_baseChange B t) ψ
  refine ⟨Additive.ofMul χ₀, ?_⟩
  change Additive.ofMul (Langlands.GroupScheme.Cartier.restrictGrp _ _ a χ₀) = χK
  have : Langlands.GroupScheme.Cartier.restrictGrp A.toCommGroupScheme B.toCommGroupScheme a χ₀ =
      CommGroupScheme.groupHom χK := by
    unfold Langlands.GroupScheme.Cartier.restrictGrp
    change _ ≫ (GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap V K)))).map χ₀ ≫
      _ = _
    rw [hχ₀]
    simp [ψ]
    rfl
  rw [this]
  rfl

/-- The affine-test Hom-scheme interface implies relative endomorphism representability. -/
theorem relativeEndomorphismRepresentability_of_affineHomSchemePiecesStatement
    (hP : AffineHomSchemePiecesStatement.{u}) :
    RelativeEndomorphismRepresentabilityStatement.{u} :=
  relativeEndomorphismRepresentability_of_affineHomSchemePieces hP neronHomExtension

end Langlands.AbelianScheme
