import Langlands.GroupScheme.Reductive.Pinning
import Langlands.GroupScheme.Reductive.RootDatumBaseChangeProof
import Langlands.GroupScheme.Reductive.AlgebraicExtensionAscent
import Langlands.GroupScheme.Torus.MaximalBaseChangeProof
import Langlands.GroupScheme.Torus.WeightBaseChangeComparison

/-! # Scalar extension of actual split pinnings -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme

private theorem tensor_one_smul {k F M : Type*} [Field k] [Field F] [Algebra k F]
    [AddCommGroup M] [Module k M] (c : k) (x : M) :
    (1 : F) ⊗ₜ[k] (c • x) = (algebraMap k F c) • ((1 : F) ⊗ₜ[k] x) := by
  simp only [TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.smul_def,
    Algebra.algebraMap_self_apply, mul_one]

private theorem lineMap_injective {F M : Type*} [Field F] [AddCommGroup M] [Module F M]
    (v : M) (hv : v ≠ 0) : Function.Injective (LinearMap.toSpanSingleton F M v) := by
  intro c d h
  have hz : (c - d) • v = 0 := by
    change c • v = d • v at h
    rw [sub_smul, h, sub_self]
  exact sub_eq_zero.mp ((smul_eq_zero.mp hz).resolve_right hv)

section WeightLines

variable {k F : Type u} [Field k] [Field F] [Algebra k F]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom]
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {i : T.toGrp ⟶ G} {J : Type u}
    {P : RootDatum J (characterLattice T) (cocharacterLattice T)} {b : P.Base}
    (p : RootPinning i P b)

local notation "bc" => algebraBaseMap k F
local notation "GF" => Functor.obj (GroupScheme.baseChange bc) G

local instance : IsAffineHom (GF).X.hom := by
  change IsAffineHom (pullback.snd G.X.hom bc)
  infer_instance

namespace RootPinning

/-- The actual scalar extension of a pinned simple-root vector. -/
def baseChangeRootVector (a : b.support) :
    weightSpace ((GroupScheme.baseChange bc).map i)
      (characterLattice.baseChange bc T (P.root a)) :=
  ⟨Lie.schemeScalarExtension (K := F) G (1 ⊗ₜ[k] p.rootVector a),
    weightSpace_baseChange_mem G i (P.root a) (p.rootVector_mem a)⟩

theorem baseChangeRootVector_ne_zero (a : b.support) :
    baseChangeRootVector (F := F) p a ≠ 0 := by
  intro h
  have he := congrArg Subtype.val h
  have hz : (1 : F) ⊗ₜ[k] p.rootVector a = 0 :=
    (Lie.schemeScalarExtension (K := F) G).injective
      (by simpa only [baseChangeRootVector, Submodule.coe_zero, LinearEquiv.map_zero] using he)
  exact p.rootVector_ne_zero a
    (by simpa only [Module.FaithfullyFlat.one_tmul_eq_zero_iff] using hz)

/-- The pulled-back weight space is the line spanned by the extended pinned vector. -/
theorem weightSpace_baseChange_eq_span (hT : IsSplitTorus T.toGrp) (a : b.support) :
    weightSpace ((GroupScheme.baseChange bc).map i)
        (characterLattice.baseChange bc T (P.root a)) =
      Submodule.span F {((baseChangeRootVector (F := F) p a).val)} := by
  dsimp only [baseChangeRootVector]
  rw [weightSpace_baseChange_eq_extendedWeightSpace hT i (P.root a)]
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨c, hc⟩ := (p.trivialization a).surjective ⟨z, hz⟩
    have hzc : z = c • p.rootVector a := by
      simpa only [p.trivialization_apply_val] using (congrArg Subtype.val hc).symm
    have hten := tensor_one_smul (F := F) c (p.rootVector a)
    rw [hzc]
    dsimp only []
    rw [hten, LinearEquiv.map_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _))
  · apply Submodule.span_le.mpr
    rintro _ ⟨rfl⟩
    exact Submodule.subset_span ⟨p.rootVector a, p.rootVector_mem a, rfl⟩

/-- The scalar extension of the chosen trivialization, with value one equal to
its actual extended pinned root vector. -/
def baseChangeTrivialization (hT : IsSplitTorus T.toGrp) (a : b.support) :
    F ≃ₗ[F] weightSpace ((GroupScheme.baseChange bc).map i)
      (characterLattice.baseChange bc T (P.root a)) :=
  by
    let W : Submodule F (Additive (lieKernel GF F)) :=
      weightSpace ((GroupScheme.baseChange bc).map i)
        (characterLattice.baseChange bc T (P.root a))
    letI : Module F W := Submodule.module W
    let v : W := baseChangeRootVector (F := F) p a
    exact LinearEquiv.ofBijective (LinearMap.toSpanSingleton F W v) (by
      constructor
      · exact lineMap_injective v (baseChangeRootVector_ne_zero p a)
      · intro y
        have hy : y.val ∈ Submodule.span F {v.val} := by
          rw [← weightSpace_baseChange_eq_span p hT a]
          exact y.property
        obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hy
        exact ⟨c, Subtype.ext hc⟩)

@[simp]
theorem baseChangeTrivialization_one (hT : IsSplitTorus T.toGrp) (a : b.support) :
    baseChangeTrivialization (F := F) p hT a 1 = baseChangeRootVector (F := F) p a :=
  one_smul F _

end RootPinning

end WeightLines

namespace SplitPinning

variable {k F : Type u} [Field k] [Field F] [Algebra k F]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    (p : SplitPinning G)

local notation "bc" => algebraBaseMap k F
local notation "GF" => Functor.obj (GroupScheme.baseChange bc) G

local instance : IsAffineHom (GF).X.hom := by
  change IsAffineHom (pullback.snd G.X.hom bc)
  infer_instance

/-- The exact transported root datum of the pulled-back split maximal torus. -/
def baseChangeRootDatum := SplitRootDatum.baseChange bc p.torus p.isSplitTorus p.rootDatum

/-- The canonical equivalence of the supplied root datum and its actual lattice pullback. -/
def baseChangeRootDatumEquiv : p.rootDatum.Equiv (p.baseChangeRootDatum (F := F)) where
  weightMap := (characterLattice.baseChangeEquiv bc p.torus p.isSplitTorus).toIntLinearEquiv
  coweightMap := (cocharacterLattice.baseChangeEquiv bc p.torus p.isSplitTorus).symm.toIntLinearEquiv
  indexEquiv := Equiv.refl p.rootIndex
  weight_coweight_transpose := by
    ext y x
    obtain ⟨z, rfl⟩ := (cocharacterLattice.baseChangeEquiv bc p.torus p.isSplitTorus).surjective y
    change (p.baseChangeRootDatum (F := F)).toLinearMap
      (characterLattice.baseChange bc p.torus x)
      (cocharacterLattice.baseChange bc p.torus z) =
      p.rootDatum.toLinearMap x
        ((cocharacterLattice.baseChangeEquiv bc p.torus p.isSplitTorus).symm
          ((cocharacterLattice.baseChangeEquiv bc p.torus p.isSplitTorus) z))
    rw [AddEquiv.symm_apply_apply]
    exact SplitRootDatum.baseChange_pairing bc p.torus p.isSplitTorus p.rootDatum x z
  root_weightMap := rfl
  coroot_coweightMap := by
    funext a
    exact (cocharacterLattice.baseChangeEquiv bc p.torus p.isSplitTorus).symm_apply_apply
      (p.rootDatum.coroot a)
  bijective_weightMap := (characterLattice.baseChangeEquiv bc p.torus p.isSplitTorus).bijective
  bijective_coweightMap := (cocharacterLattice.baseChangeEquiv bc p.torus p.isSplitTorus).symm.bijective

/-- Transport of the actual supplied base, preserving its original root indices. -/
def baseChangeBase : (p.baseChangeRootDatum (F := F)).Base :=
  p.base.map (p.baseChangeRootDatumEquiv (F := F))

@[simp]
theorem baseChangeBase_support : (p.baseChangeBase (F := F)).support = p.base.support := by
  classical
  simp only [baseChangeBase, RootPairing.Base.support_map_eq, baseChangeRootDatumEquiv,
    Equiv.coe_refl, Finset.image_id]

/-- The supplied simple-root index set is unchanged by canonical lattice pullback. -/
def baseChangeSimpleEquiv : p.base.support ≃ (p.baseChangeBase (F := F)).support :=
  Equiv.subtypeEquivRight fun a => by rw [baseChangeBase_support]

/-- Reducedness is preserved by the actual character-lattice equivalence. -/
theorem isReduced_baseChangeRootDatum : (p.baseChangeRootDatum (F := F)).IsReduced := by
  have := p.isReduced
  refine ⟨fun a c h => ?_⟩
  have h' : ¬ LinearIndependent ℤ ![p.rootDatum.root a, p.rootDatum.root c] := by
    intro hli
    apply h
    let f : characterLattice p.torus ≃ₗ[ℤ]
        characterLattice ((CommGroupScheme.baseChange bc).obj p.torus) :=
      (characterLattice.baseChangeEquiv bc p.torus p.isSplitTorus).toIntLinearEquiv
    convert hli.map' f.toLinearMap (LinearMap.ker_eq_bot.mpr f.injective) using 1
    ext j
    fin_cases j <;> rfl
  rcases RootPairing.IsReduced.eq_or_eq_neg a c h' with h | h
  · exact Or.inl (congrArg (characterLattice.baseChange bc p.torus) h)
  · exact Or.inr (by
      simpa only [baseChangeRootDatum, SplitRootDatum.baseChange_root, map_neg] using
        (congrArg (characterLattice.baseChange bc p.torus) h))

variable [Algebra.IsAlgebraic k F]

/-- Scalar extension of the actual supplied split pinning along an algebraic field extension. -/
def baseChange : SplitPinning GF := by
  have := p.isConnectedReductive.smooth
  exact {
    isConnectedReductive := p.isConnectedReductive.baseChange_of_algebraicExtension
    torus := (CommGroupScheme.baseChange bc).obj p.torus
    inclusion := (GroupScheme.baseChange bc).map p.inclusion
    isSplitTorus := p.isSplitTorus.baseChange bc
    isMaximalTorus := (maximalTorusBaseChange k F G p.torus p.inclusion
      p.isMaximalTorus.1 p.isMaximalTorus.2.1).mp p.isMaximalTorus
    rootIndex := p.rootIndex
    rootDatum := p.baseChangeRootDatum (F := F)
    isRootDatum := p.isRootDatum.baseChange (K := F) G p.torus p.isSplitTorus p.inclusion
    isReduced := p.isReduced_baseChangeRootDatum (F := F)
    base := p.baseChangeBase (F := F)
    pinning := { trivialization := fun a =>
      (RootPinning.baseChangeTrivialization p.pinning p.isSplitTorus
        ((p.baseChangeSimpleEquiv (F := F)).symm a)) } }

/-- The pulled-back pinning retains the actual scalar extension of every chosen root vector. -/
theorem baseChange_rootVector (a : p.base.support) :
    haveI := p.isConnectedReductive.smooth
    (p.baseChange (F := F)).pinning.rootVector (p.baseChangeSimpleEquiv (F := F) a) =
      Lie.schemeScalarExtension (K := F) G (1 ⊗ₜ[k] p.pinning.rootVector a) := by
  have := p.isConnectedReductive.smooth
  change (RootPinning.baseChangeTrivialization (F := F) p.pinning p.isSplitTorus
    ((p.baseChangeSimpleEquiv (F := F)).symm (p.baseChangeSimpleEquiv (F := F) a)) 1).val = _
  rw [Equiv.symm_apply_apply, RootPinning.baseChangeTrivialization_one]
  rfl

end SplitPinning

end Langlands.GroupScheme
