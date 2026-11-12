import Langlands.AlgebraicGeometry.Picard.DualKernelCharacterNaturality
import Langlands.AlgebraicGeometry.Picard.DualKernelCharacterAdditivity
import Langlands.AlgebraicGeometry.Picard.FieldDualKernelCharacterBijectiveProof

/-! # Cartier duality of actual isogeny kernels as group-valued functors -/

universe u

open CategoryTheory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

noncomputable section

namespace Langlands.GroupScheme

variable {S : Scheme.{u}} (G : Grp (Over S)) [IsCommMonObj G.X]

/-- The actual points of a commutative group scheme, written additively. -/
def additivePoints : (Over S)ᵒᵖ ⥤ AddCommGrpCat.{u} where
  obj T := AddCommGrpCat.of (Additive (T.unop ⟶ G.X))
  map {T U} b := AddCommGrpCat.ofHom
    { toFun x := Additive.ofMul (b.unop ≫ x.toMul)
      map_zero' := MonObj.comp_one b.unop
      map_add' x y := MonObj.comp_mul b.unop x.toMul y.toMul }
  map_id T := by
    ext x
    change (𝟙 T.unop) ≫ x.toMul = x.toMul
    exact Category.id_comp x.toMul
  map_comp b c := by
    ext x
    change (c.unop ≫ b.unop) ≫ x.toMul = c.unop ≫ (b.unop ≫ x.toMul)
    exact Category.assoc c.unop b.unop x.toMul

@[simp] theorem additivePoints_map {T U : Over S} (b : U ⟶ T)
    (x : Additive (T ⟶ G.X)) :
    (additivePoints G).map b.op x = Additive.ofMul (b ≫ x.toMul) := rfl

end Langlands.GroupScheme

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules Langlands.SchemeModule
open Langlands.GroupScheme

section Relative

variable (preservation : pullbackTensorComparisonIsIsoStatement.{u})
  (composition : PullbackTensorCompositionStatement.{u})
  (unitCoherence : PullbackTensorUnitCoherenceStatement.{u})
  (associativity : ExplicitPullbackTensorAssociativityStatement.{u})
  (comparison : TensorMonoidalLeftUnitorComparisonStatement.{u})
  (symmetry : PullbackTensorSymmetryStatement.{u})
  (stability : PicardZeroPullbackStatement.{u})
  {S : Scheme.{u}} {A B : AbelianScheme S}
  (hA : HasDualScheme A) (hB : HasDualScheme B)
  (MA : LineBundle ((relativeSpace A.X.hom).obj (dualScheme A hA)))
  (evaluationA : tensorObj (poincareFamily A hA).obj.carrier MA.obj ≅
    structureSheaf ((relativeSpace A.X.hom).obj (dualScheme A hA)))
  (MB : LineBundle ((relativeSpace B.X.hom).obj (dualScheme B hB)))
  (evaluationB : tensorObj (poincareFamily B hB).obj.carrier MB.obj ≅
    structureSheaf ((relativeSpace B.X.hom).obj (dualScheme B hB)))
  (f : A ⟶ B)

local notation "df" => Langlands.CommGroupScheme.groupHom
  (dualCommGroupSchemeMapFromEvaluation preservation composition unitCoherence associativity
    comparison symmetry stability hA hB MA evaluationA MB evaluationB f)
local notation "beta" => dualKernelPointCharacter hA stability f hB preservation composition
  unitCoherence associativity comparison symmetry MA evaluationA MB evaluationB
local notation "betaAdd" => dualKernelPointCharacterAddHom hA stability f hB preservation
  composition unitCoherence associativity comparison symmetry MA evaluationA MB evaluationB

/-- The normalized Poincare kernel character as a morphism of abelian-group presheaves. -/
def dualKernelCharacterAddNatTrans :
    additivePoints (GroupScheme.kernel df) ⟶ Cartier.characters (kernelCommGroupScheme f) where
  app T := AddCommGrpCat.ofHom (betaAdd T.unop)
  naturality T U b := by
    ext x
    exact dualKernelPointCharacter_restrict hA stability f hB b.unop preservation composition
      unitCoherence associativity comparison symmetry MA evaluationA MB evaluationB x.toMul

/-- Its component is the existing actual normalized kernel character. -/
@[simp] theorem dualKernelCharacterAddNatTrans_app (T : Over S)
    (x : Additive (T ⟶ (GroupScheme.kernel df).X)) :
    (dualKernelCharacterAddNatTrans preservation composition unitCoherence associativity
      comparison symmetry stability hA hB MA evaluationA MB evaluationB f).app (op T) x =
      beta T x.toMul := rfl

end Relative

section Field

variable (preservation : pullbackTensorComparisonIsIsoStatement.{u})
  (composition : PullbackTensorCompositionStatement.{u})
  (unitCoherence : PullbackTensorUnitCoherenceStatement.{u})
  (associativity : ExplicitPullbackTensorAssociativityStatement.{u})
  (comparison : TensorMonoidalLeftUnitorComparisonStatement.{u})
  (symmetry : PullbackTensorSymmetryStatement.{u})
  (stability : PicardZeroPullbackStatement.{u})
  {k : Type u} [Field k] {A B : AbelianScheme (Spec (.of k))}
  (hA : HasDualScheme A) (hB : HasDualScheme B)
  (MA : LineBundle ((relativeSpace A.X.hom).obj (dualScheme A hA)))
  (evaluationA : tensorObj (poincareFamily A hA).obj.carrier MA.obj ≅
    structureSheaf ((relativeSpace A.X.hom).obj (dualScheme A hA)))
  (MB : LineBundle ((relativeSpace B.X.hom).obj (dualScheme B hB)))
  (evaluationB : tensorObj (poincareFamily B hB).obj.carrier MB.obj ≅
    structureSheaf ((relativeSpace B.X.hom).obj (dualScheme B hB)))
  (f : A ⟶ B)

local notation "df" => Langlands.CommGroupScheme.groupHom
  (dualCommGroupSchemeMapFromEvaluation preservation composition unitCoherence associativity
    comparison symmetry stability hA hB MA evaluationA MB evaluationB f)
local notation "beta" => dualKernelPointCharacter hA stability f hB preservation composition
  unitCoherence associativity comparison symmetry MA evaluationA MB evaluationB
local notation "betaAdd" => dualKernelPointCharacterAddHom hA stability f hB preservation
  composition unitCoherence associativity comparison symmetry MA evaluationA MB evaluationB

variable (hf : IsIsogeny f)

/-- Actual Cartier duality on every test scheme over a field, as an additive equivalence. -/
def fieldDualKernelCharacterEquiv (T : Over (Spec (.of k))) :
    Additive (T ⟶ (GroupScheme.kernel df).X) ≃+
      (Cartier.characters (kernelCommGroupScheme f)).obj (op T) :=
  AddEquiv.ofBijective (betaAdd T)
    (fieldDualKernelCharacterBijective preservation composition unitCoherence associativity
      comparison symmetry stability k A B hA hB MA evaluationA MB evaluationB f hf T)

@[simp] theorem fieldDualKernelCharacterEquiv_apply (T : Over (Spec (.of k)))
    (x : Additive (T ⟶ (GroupScheme.kernel df).X)) :
    fieldDualKernelCharacterEquiv preservation composition unitCoherence associativity
      comparison symmetry stability hA hB MA evaluationA MB evaluationB f hf T x =
      beta T x.toMul := rfl

/-- The actual dual kernel represents the relative Cartier-character functor as groups. -/
def fieldDualKernelCartierIso :
    additivePoints (GroupScheme.kernel df) ≅ Cartier.characters (kernelCommGroupScheme f) :=
  NatIso.ofComponents
    (fun T => (fieldDualKernelCharacterEquiv preservation composition unitCoherence
      associativity comparison symmetry stability hA hB MA evaluationA MB evaluationB f hf
      T.unop).toAddCommGrpIso)
    (by
      intro T U b
      ext x
      exact dualKernelPointCharacter_restrict hA stability f hB b.unop preservation composition
        unitCoherence associativity comparison symmetry MA evaluationA MB evaluationB x.toMul)

/-- The forward map of the isomorphism is exactly the normalized Poincare character. -/
@[simp] theorem fieldDualKernelCartierIso_hom :
    (fieldDualKernelCartierIso preservation composition unitCoherence associativity comparison
      symmetry stability hA hB MA evaluationA MB evaluationB f hf).hom =
      dualKernelCharacterAddNatTrans preservation composition unitCoherence associativity
        comparison symmetry stability hA hB MA evaluationA MB evaluationB f := by
  ext T x
  rfl

/-- The same Cartier duality with actual homomorphisms over each test scheme as target. -/
def fieldDualKernelCharacterHomIso :
    additivePoints (GroupScheme.kernel df) ≅
      Cartier.characterHomFunctor (kernelCommGroupScheme f) :=
  fieldDualKernelCartierIso preservation composition unitCoherence associativity comparison
    symmetry stability hA hB MA evaluationA MB evaluationB f hf ≪≫
      Cartier.characterHomNatIso (kernelCommGroupScheme f)

include hf in
/-- Every character, including on nonreduced tests, comes from a unique actual dual-kernel point. -/
theorem fieldDualKernelCharacter_existsUnique (T : Over (Spec (.of k)))
    (chi : (Cartier.characters (kernelCommGroupScheme f)).obj (op T)) :
    ∃! x : T ⟶ (GroupScheme.kernel df).X, beta T x = chi := by
  obtain ⟨x, hx⟩ := (fieldDualKernelCharacterEquiv preservation composition unitCoherence
    associativity comparison symmetry stability hA hB MA evaluationA MB evaluationB f hf
    T).surjective chi
  refine ⟨x.toMul, hx, ?_⟩
  intro y hy
  exact (fieldDualKernelCharacterBijective preservation composition unitCoherence associativity
    comparison symmetry stability k A B hA hB MA evaluationA MB evaluationB f hf T).injective
      (hy.trans hx.symm)

end Field
end Langlands.AbelianScheme
