import Langlands.Representation.Category.Basic
import Langlands.Representation.Smooth.FixedVectors.LengthCriterionProof
import Langlands.Topology.CompactOpen.OpenSubgroup
import Mathlib.CategoryTheory.Center.Linear
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-! # The operator span of the categorical centre on a smooth representation

Elementary linear algebra for Renard VI.10.8. No Bernstein decomposition,
admissibility theorem, Howe theorem or reductive structure is used here.
-/

noncomputable section

open CategoryTheory

namespace Langlands.SmoothRep

universe uR uG uV

variable {R : Type uR} [Field R] {G : Type uG} [Group G] [TopologicalSpace G]

/-- The scalar span of the actual operators induced by the categorical centre. -/
def centerOperatorSpan (A : SmoothRep.{uR, uG, uV} R G) : Submodule R (Module.End R A) :=
  Submodule.span R (Set.range fun z : CatCenter (SmoothRep.{uR, uG, uV} R G) =>
    (hom (z.app A)).toLinearMap)

/-- Finite generation of each compact-open fixed space by actual centre operators. -/
def IsCenterAdmissible (A : SmoothRep.{uR, uG, uV} R G) : Prop :=
  ∀ K : OpenSubgroup G, IsCompact (K : Set G) →
    ∃ (n : ℕ) (s : Fin n → A),
      (∀ i, ∀ g ∈ K, A.representation g (s i) = s i) ∧
      ∀ x : A, (∀ g ∈ K, A.representation g x = x) →
        ∃ z : Fin n → CatCenter (SmoothRep.{uR, uG, uV} R G),
          x = ∑ i, hom ((z i).app A) (s i)

/-- Every operator in the centre span is equivariant. -/
theorem centerOperatorSpan_commutes (A : SmoothRep.{uR, uG, uV} R G)
    {f : Module.End R A} (hf : f ∈ centerOperatorSpan A) (g : G) (x : A) :
    f (A.representation g x) = A.representation g (f x) := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨z, rfl⟩ := hf
    exact Representation.IntertwiningMap.isIntertwining _ _ (hom (z.app A)) g x
  | zero => simp
  | add f h hf hh ihf ihh => simp only [LinearMap.add_apply, ihf, ihh, map_add]
  | smul a f hf ih => simp only [LinearMap.smul_apply, ih, map_smul]

/-- Evaluate a centre-span operator on a fixed vector, retaining fixedness. -/
def centerFixedEvaluation (A : SmoothRep.{uR, uG, uV} R G) (H : Subgroup G)
    (x : fixedVectors A.representation H) :
    centerOperatorSpan A →ₗ[R] fixedVectors A.representation H where
  toFun f := ⟨f.val x.val, by
    intro g
    change A.representation (g : G) (f.val x.val) = f.val x.val
    rw [← centerOperatorSpan_commutes A f.property]
    exact congrArg f.val (x.property g)⟩
  map_add' _ _ := by ext; rfl
  map_smul' _ _ := by ext; rfl

/-- Evaluation on a family of fixed vectors. -/
def centerFixedFamilyEvaluation (A : SmoothRep.{uR, uG, uV} R G) (H : Subgroup G)
    {n : ℕ} (s : Fin n → fixedVectors A.representation H) :
    centerOperatorSpan A →ₗ[R] (Fin n → fixedVectors A.representation H) :=
  LinearMap.pi fun i => centerFixedEvaluation A H (s i)

/-- Equivariant operators are determined by their values on group-algebra generators. -/
theorem centerFixedFamilyEvaluation_injective (A : SmoothRep.{uR, uG, uV} R G)
    (H : Subgroup G) {n : ℕ} (s : Fin n → fixedVectors A.representation H)
    (hgen : Submodule.span (MonoidAlgebra R G)
      (Set.range fun i => A.representation.asModuleEquiv.symm (s i).val) = ⊤) :
    Function.Injective (centerFixedFamilyEvaluation A H s) := by
  intro f h heq
  let f' : A.representation.IntertwiningMap A.representation :=
    f.val.intertwiningMap_of_isIntertwiningMap _ _
      (fun g x => centerOperatorSpan_commutes A f.property g x)
  let h' : A.representation.IntertwiningMap A.representation :=
    h.val.intertwiningMap_of_isIntertwiningMap _ _
      (fun g x => centerOperatorSpan_commutes A h.property g x)
  have hh : Representation.IntertwiningMap.equivLinearMapAsModule _ _ f' =
      Representation.IntertwiningMap.equivLinearMapAsModule _ _ h' := by
    apply LinearMap.ext_on_range hgen
    intro i
    exact congrArg Subtype.val (congrFun heq i)
  apply Subtype.ext
  exact congrArg Representation.IntertwiningMap.toLinearMap
    ((Representation.IntertwiningMap.equivLinearMapAsModule _ _).injective hh)

/-- Finite type and admissibility imply finite-dimensional centre operator span.
The proof evaluates on common open-fixed generators; compactness is unnecessary. -/
theorem finite_centerOperatorSpan_of_finiteType_admissible
    (A : SmoothRep.{uR, uG, uV} R G)
    (hfin : Module.Finite (MonoidAlgebra R G) A.representation.asModule)
    (hadm : A.IsAdmissible) : FiniteDimensional R (centerOperatorSpan A) := by
  obtain ⟨n, v, K, hgen, hfix, -⟩ :=
    commonFixedGenerators R G A A.representation A.isSmooth hfin
  let s : Fin n → fixedVectors A.representation K.toSubgroup := fun i => ⟨v i, hfix i⟩
  have : FiniteDimensional R (fixedVectors A.representation K.toSubgroup) := hadm.2 K
  exact FiniteDimensional.of_injective (centerFixedFamilyEvaluation A K.toSubgroup s)
    (centerFixedFamilyEvaluation_injective A K.toSubgroup s hgen)

/-- A finite-dimensional centre span and finitely many centre generators make
that fixed-vector space finite-dimensional. -/
theorem finite_fixedVectors_of_center_generators
    (A : SmoothRep.{uR, uG, uV} R G) (H : Subgroup G)
    (hcenter : FiniteDimensional R (centerOperatorSpan A))
    {n : ℕ} (s : Fin n → fixedVectors A.representation H)
    (hgen : ∀ x : fixedVectors A.representation H,
      ∃ z : Fin n → CatCenter (SmoothRep.{uR, uG, uV} R G),
        x.val = ∑ i, hom ((z i).app A) (s i).val) :
    FiniteDimensional R (fixedVectors A.representation H) := by
  classical
  let := hcenter
  let f : (Fin n → centerOperatorSpan A) →ₗ[R] fixedVectors A.representation H :=
    ∑ i, (centerFixedEvaluation A H (s i)).comp (LinearMap.proj i)
  apply Module.Finite.of_surjective f
  intro x
  obtain ⟨z, hz⟩ := hgen x
  refine ⟨fun i => ⟨(hom ((z i).app A)).toLinearMap,
    Submodule.subset_span ⟨z i, rfl⟩⟩, ?_⟩
  apply Subtype.ext
  simpa [f, centerFixedEvaluation, LinearMap.sum_apply] using hz.symm

/-- Admissibility implies centre admissibility by scalar natural transformations. -/
theorem IsAdmissible.isCenterAdmissible (A : SmoothRep.{uR, uG, uV} R G)
    (hA : A.IsAdmissible) : A.IsCenterAdmissible := by
  classical
  intro K _
  let : Module.Finite R (fixedVectors A.representation K.toSubgroup) := hA.2 K
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := R)
    (M := fixedVectors A.representation K.toSubgroup)
  refine ⟨n, fun i => (s i).val, ?_, ?_⟩
  · intro i g hg
    exact (s i).property ⟨g, hg⟩
  · intro x hx
    let y : fixedVectors A.representation K.toSubgroup := ⟨x, fun g => hx g g.property⟩
    have hy : y ∈ Submodule.span R (Set.range s) := hs ▸ Submodule.mem_top
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun R).mp hy
    refine ⟨fun i => Linear.toCatCenter R (SmoothRep.{uR, uG, uV} R G) (c i), ?_⟩
    change x = ∑ i, c i • (s i).val
    simpa [y] using (congrArg Subtype.val hc).symm

/-- Centre admissibility and finite-dimensional centre action imply admissibility
for locally compact nonarchimedean groups. Compact-open cofinality yields the
all-open-subgroups convention of `IsAdmissible`. -/
theorem isAdmissible_of_centerAdmissible_centerFinite
    [NonarchimedeanGroup G] [WeaklyLocallyCompactSpace G]
    (A : SmoothRep.{uR, uG, uV} R G) (hadm : A.IsCenterAdmissible)
    (hcenter : FiniteDimensional R (centerOperatorSpan A)) : A.IsAdmissible := by
  refine ⟨A.isSmooth, ?_⟩
  intro U
  obtain ⟨K, hK, hKU⟩ := openSubgroupContainsCompactOpen G U
  obtain ⟨n, s, hs, hgen⟩ := hadm K hK
  let t : Fin n → fixedVectors A.representation K.toSubgroup :=
    fun i => ⟨s i, fun g => hs i g g.property⟩
  have : FiniteDimensional R (fixedVectors A.representation K.toSubgroup) :=
    finite_fixedVectors_of_center_generators A K.toSubgroup hcenter t
      (fun x => hgen x.val (fun g hg => x.property ⟨g, hg⟩))
  exact Module.Finite.of_injective
    (Submodule.inclusion (show fixedVectors A.representation U.toSubgroup ≤
      fixedVectors A.representation K.toSubgroup from fun x hx g => hx ⟨g, hKU g.property⟩))
    (Submodule.inclusion_injective _)

end Langlands.SmoothRep
