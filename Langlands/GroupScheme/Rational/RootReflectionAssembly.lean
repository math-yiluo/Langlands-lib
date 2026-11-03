import Langlands.GroupScheme.Rational.RootFiniteness
import Mathlib.LinearAlgebra.RootSystem.Basic

/-! # Assembling an actual relative root system from integral normalizer reflections -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open Langlands.LinearAlgebra.RationalSpan

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  (i : T.toGrp ⟶ G) [IsAffineHom G.X.hom]

namespace RelativeRootSystem

/-- An actual relative root, regarded as a vector in its rational span. -/
def rootVector (α : relativeRoots i) : relativeRootSpan i :=
  ⟨toRat α.val, toRat_mem_ratSpan α.property⟩

/-- The actual relative-root vectors span the existing relative root span. -/
theorem span_range_rootVector :
    Submodule.span ℚ (Set.range (rootVector i)) = ⊤ := by
  apply (Submodule.span_range_subtype_eq_top_iff _ _).mpr
  change Submodule.span ℚ (Set.range fun α : relativeRoots i => toRat α.val) =
    Submodule.span ℚ (toRat '' relativeRoots i)
  congr 1
  exact Set.range_comp _ _ |>.trans (by rw [Subtype.range_coe_subtype]; rfl)

/-- For a split torus, different actual roots give different vectors. -/
def rootEmbedding (hT : IsSplitTorus T.toGrp) : relativeRoots i ↪ relativeRootSpan i where
  toFun := rootVector i
  inj' := fun _ _ h => Subtype.ext
    (hT.character_toRat_injective (congrArg Subtype.val h))

/-- Evaluation of the actual lattice pairing with a cocharacter, extended to the
rational root span. -/
def corootFunctional (ν : cocharacterLattice T) : Module.Dual ℚ (relativeRootSpan i) :=
  ((TensorProduct.AlgebraTensorModule.rid ℤ ℚ ℚ).toLinearMap.comp
    (((latticePairing T).flip ν).baseChange ℚ)).comp (relativeRootSpan i).subtype

theorem corootFunctional_rootVector (ν : cocharacterLattice T) (α : relativeRoots i) :
    corootFunctional i ν (rootVector i α) = (latticePairing T α.val ν : ℚ) := by
  simp [corootFunctional, rootVector, toRat, zsmul_eq_mul]

end RelativeRootSystem

variable [Mono i.hom.hom.left]

/-- Integral reflection data in the actual torus: each actual root has a
cocharacter pairing to two and a normalizing rational point acting by its
lattice reflection formula. This is input data, not an existence assertion. -/
structure RelativeRootReflectionData where
  coroot : relativeRoots i → cocharacterLattice T
  representative : relativeRoots i → normalizerPoints i
  pair_self : ∀ α, latticePairing T α.val (coroot α) = 2
  action : ∀ α (χ : characterLattice T),
    weylAction i (representative α) χ =
      χ - latticePairing T χ (coroot α) • α.val

namespace RelativeRootReflectionData

open RelativeRootSystem

variable {i} (D : RelativeRootReflectionData i)

/-- The normalizing reflection representative sends each actual root vector to
the vector given by the integral reflection formula. -/
theorem reflection_rootVector (α β : relativeRoots i) :
    Module.preReflection (rootVector i α) (corootFunctional i (D.coroot α))
      (rootVector i β) =
        rootVector i
          ⟨weylAction i (D.representative α) β.val,
            weylAction_mapsTo_relativeRoots i (D.representative α) β.property⟩ := by
  apply Subtype.ext
  change toRat β.val -
      corootFunctional i (D.coroot α) (rootVector i β) • toRat α.val = _
  rw [corootFunctional_rootVector]
  change _ = toRat (weylAction i (D.representative α) β.val)
  rw [D.action, map_sub, map_zsmul, Int.cast_smul_eq_zsmul]

theorem mapsTo_preReflection (α : relativeRoots i) :
    Set.MapsTo (Module.preReflection (rootVector i α) (corootFunctional i (D.coroot α)))
      (Set.range (rootVector i)) (Set.range (rootVector i)) := by
  rintro _ ⟨β, rfl⟩
  exact ⟨_, (D.reflection_rootVector α β).symm⟩

/-- Finiteness and reflection stability force the restricted coroot functionals
to be injective; this is not an additional structural assumption. -/
theorem corootFunctional_injective (hT : IsSplitTorus T.toGrp)
    (hfinite : (relativeRoots i).Finite) :
    Function.Injective (fun α => corootFunctional i (D.coroot α)) := by
  let := hfinite.fintype
  have : IsAddTorsionFree (relativeRootSpan i) := .of_isTorsionFree ℚ _
  have htwo (α : relativeRoots i) :
      corootFunctional i (D.coroot α) (rootVector i α) = 2 := by
    rw [corootFunctional_rootVector, D.pair_self]
    norm_num
  intro α β h
  change corootFunctional i (D.coroot α) = corootFunctional i (D.coroot β) at h
  apply (rootEmbedding i hT).injective
  change rootVector i α = rootVector i β
  exact Module.eq_of_mapsTo_reflection_of_mem (Set.finite_range (rootVector i))
    (htwo α) (htwo β) (by rw [← h]; exact htwo α) (by rw [h]; exact htwo β)
    (D.mapsTo_preReflection α) (D.mapsTo_preReflection β) (Set.mem_range_self β)

/-- The evaluation root pairing on the existing actual root span, constructed
from finite integral normalizer reflection data. -/
def rootPairing (hT : IsSplitTorus T.toGrp) (hfinite : (relativeRoots i).Finite) :
    RootPairing (relativeRoots i) ℚ (relativeRootSpan i)
      (Module.Dual ℚ (relativeRootSpan i)) :=
  letI := hfinite.fintype
  have : FiniteDimensional ℚ (relativeRootSpan i) :=
    FiniteDimensional.span_of_finite ℚ (hfinite.image toRat)
  RootPairing.mk'' (Module.Dual.eval ℚ (relativeRootSpan i)) (rootEmbedding i hT)
    ⟨_, D.corootFunctional_injective hT hfinite⟩
    (fun α => by
      change corootFunctional i (D.coroot α) (rootVector i α) = 2
      rw [corootFunctional_rootVector, D.pair_self]
      norm_num)
    (D.mapsTo_preReflection) (span_range_rootVector i)

theorem rootPairing_toLinearMap (hT : IsSplitTorus T.toGrp)
    (hfinite : (relativeRoots i).Finite) :
    (D.rootPairing hT hfinite).toLinearMap = Module.Dual.eval ℚ (relativeRootSpan i) :=
  rfl

theorem rootPairing_root (hT : IsSplitTorus T.toGrp)
    (hfinite : (relativeRoots i).Finite) (α : relativeRoots i) :
    (D.rootPairing hT hfinite).root α = rootVector i α :=
  rfl

theorem rootPairing_coroot (hT : IsSplitTorus T.toGrp)
    (hfinite : (relativeRoots i).Finite) (α : relativeRoots i) :
    (D.rootPairing hT hfinite).coroot α = corootFunctional i (D.coroot α) :=
  rfl

theorem rootPairing_isRootSystem (hT : IsSplitTorus T.toGrp)
    (hfinite : (relativeRoots i).Finite) :
    (D.rootPairing hT hfinite).IsRootSystem := by
  let := hfinite.fintype
  have : FiniteDimensional ℚ (relativeRootSpan i) :=
    FiniteDimensional.span_of_finite ℚ (hfinite.image toRat)
  unfold rootPairing
  exact RootPairing.isRootSystem_mk''
    (p := Module.Dual.eval ℚ (relativeRootSpan i))
    (root := rootEmbedding i hT)
    (coroot := ⟨_, D.corootFunctional_injective hT hfinite⟩)
    (hsp := span_range_rootVector i)
    (fun α β => ⟨latticePairing T α.val (D.coroot β),
      (corootFunctional_rootVector i _ α).symm⟩)

theorem rootPairing_isCrystallographic (hT : IsSplitTorus T.toGrp)
    (hfinite : (relativeRoots i).Finite) :
    (D.rootPairing hT hfinite).IsCrystallographic := by
  refine ⟨fun α β => ⟨latticePairing T α.val (D.coroot β), ?_⟩⟩
  exact (corootFunctional_rootVector i _ α).symm

theorem rootPairing_root_image (hT : IsSplitTorus T.toGrp)
    (hfinite : (relativeRoots i).Finite) :
    Subtype.val '' Set.range (D.rootPairing hT hfinite).root =
      toRat '' relativeRoots i := by
  change Subtype.val '' Set.range (rootVector i) = _
  ext x
  constructor
  · rintro ⟨_, ⟨α, rfl⟩, rfl⟩
    exact ⟨α.val, α.property, rfl⟩
  · rintro ⟨α, hα, rfl⟩
    exact ⟨rootVector i ⟨α, hα⟩, Set.mem_range_self _, rfl⟩

/-- Each constructed root reflection is the action of its actual normalizing
rational representative. -/
theorem reflection_eq_relativeWeylAction (hT : IsSplitTorus T.toGrp)
    (hfinite : (relativeRoots i).Finite) (α : relativeRoots i) :
    (D.rootPairing hT hfinite).reflection α =
      relativeWeylAction i (QuotientGroup.mk (D.representative α)) := by
  apply LinearEquiv.toLinearMap_injective
  apply LinearMap.ext_on_range (span_range_rootVector i)
  intro β
  change Module.preReflection (rootVector i α) (corootFunctional i (D.coroot α))
      (rootVector i β) = _
  rw [D.reflection_rootVector]
  exact (relativeWeylAction_mk_toRat i (D.representative α) β.property).symm

/-- The image of the constructed Weyl group is exactly the subgroup generated
by the actions of the chosen normalizing reflection representatives. -/
theorem weylGroup_image (hT : IsSplitTorus T.toGrp)
    (hfinite : (relativeRoots i).Finite) :
    (D.rootPairing hT hfinite).weylGroup.map
        (RootPairing.Equiv.weightHom (D.rootPairing hT hfinite)) =
      Subgroup.closure (Set.range fun α =>
        relativeWeylAction i (QuotientGroup.mk (D.representative α))) := by
  rw [← MonoidHom.domRestrict_range, RootPairing.range_weylGroup_weightHom]
  congr 2
  funext α
  exact D.reflection_eq_relativeWeylAction hT hfinite α

/-- Integral normalizer reflections, generation of the actual quotient, and
faithfulness on the actual root span suffice for the complete published
relative-root-system predicate. The structural inputs remain explicit. -/
theorem hasRelativeRootSystem (hT : IsSplitTorus T.toGrp)
    (hfinite : (relativeRoots i).Finite)
    (hgenerate : Subgroup.closure (Set.range fun α =>
      (QuotientGroup.mk (D.representative α) : relativeWeylGroup i)) = ⊤)
    (hfaithful : Function.Injective (relativeWeylAction i)) :
    HasRelativeRootSystem i := by
  let := hfinite.fintype
  refine ⟨relativeRoots i, inferInstance, D.rootPairing hT hfinite,
    D.rootPairing_isRootSystem hT hfinite,
    D.rootPairing_isCrystallographic hT hfinite, rfl,
    D.rootPairing_root_image hT hfinite, ?_, hfaithful⟩
  rw [D.weylGroup_image]
  have h := congrArg (Subgroup.map (relativeWeylAction i)) hgenerate
  rw [MonoidHom.map_closure, ← Set.range_comp, Subgroup.map_top] at h
  exact h

end RelativeRootReflectionData

end Langlands.GroupScheme
