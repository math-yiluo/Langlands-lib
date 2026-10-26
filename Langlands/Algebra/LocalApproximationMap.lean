import Langlands.Algebra.LocalApproximationSystem

/-! # Compatible maps of local module approximation systems -/

universe uI uA uB uE uF uR uS uM uN

namespace Langlands.Algebra

variable {ι : Type uI} [Preorder ι] [Nonempty ι] [IsDirectedOrder ι]
  {R : Type uR} {S : Type uS} [CommRing R] [CommRing S]
  [IsLocalRing R] [IsLocalRing S] [Algebra R S] [IsLocalHom (algebraMap R S)]
  {D : LocalAlgebraSystem.{uI, uA, uB} ι R S}
  {M : Type uM} {N : Type uN} [AddCommGroup M] [AddCommGroup N]
  [Module S M] [Module S N]

namespace LocalModuleSystem

/-- Component-linear maps on the given diagrams inducing the specified `S`-linear target map. -/
structure CompatibleMap
    (E : LocalModuleSystem.{uI, uA, uB, uE} D M)
    (F : LocalModuleSystem.{uI, uA, uB, uF} D N) (f : M →ₗ[S] N) where
  component : ∀ i, E.obj i →ₗ[D.alg i] F.obj i
  map_comm : ∀ i j (h : i ≤ j) m,
    component j (E.map i j h m) = F.map i j h (component i m)
  ιM_comm : ∀ i m, F.ιM i (component i m) = f (E.ιM i m)

namespace CompatibleMap

variable {E : LocalModuleSystem.{uI, uA, uB, uE} D M}
  {F : LocalModuleSystem.{uI, uA, uB, uF} D N} {f : M →ₗ[S] N}

/-- Both supplied systems satisfy the existing six-clause approximation predicate. -/
def IsApproximation (_φ : CompatibleMap E F f) : Prop :=
  E.IsApproximation ∧ F.IsApproximation

variable (φ : CompatibleMap E F f)

/-- The actual additive map on the two direct limits, induced by the component maps. -/
noncomputable def colimitMap :
    @AddCommGroup.DirectLimit ι _ E.obj _ (Classical.decEq ι)
      (fun i j h ↦ (E.map i j h).toAddMonoidHom) →+
    @AddCommGroup.DirectLimit ι _ F.obj _ (Classical.decEq ι)
      (fun i j h ↦ (F.map i j h).toAddMonoidHom) := by
  classical
  exact AddCommGroup.DirectLimit.map (fun i ↦ (φ.component i).toAddMonoidHom)
    (fun i j h ↦ by
      ext m
      exact φ.map_comm i j h m)

/-- The induced additive map has the specified value on each component. -/
@[simp] theorem colimitMap_of (i : ι) (m : E.obj i) :
    letI := Classical.decEq ι
    φ.colimitMap (AddCommGroup.DirectLimit.of E.obj
      (fun i j h ↦ (E.map i j h).toAddMonoidHom) i m) =
    AddCommGroup.DirectLimit.of F.obj
      (fun i j h ↦ (F.map i j h).toAddMonoidHom) i (φ.component i m) := by
  classical
  exact AddCommGroup.DirectLimit.map_apply_of _ _ m

/-- The induced map commutes with the actual comparison maps to the target modules. -/
theorem moduleColimitMap_comp :
    F.moduleColimitMap.comp φ.colimitMap =
      f.toAddMonoidHom.comp E.moduleColimitMap := by
  classical
  apply AddCommGroup.DirectLimit.hom_ext
  intro i
  ext m
  simp only [AddMonoidHom.comp_apply, colimitMap_of, moduleColimitMap_of]
  exact φ.ιM_comm i m

/-- Pointwise form of the commuting square with the prescribed target map. -/
@[simp] theorem moduleColimitMap_colimitMap
    (x : @AddCommGroup.DirectLimit ι _ E.obj _ (Classical.decEq ι)
      (fun i j h ↦ (E.map i j h).toAddMonoidHom)) :
    F.moduleColimitMap (φ.colimitMap x) = f (E.moduleColimitMap x) :=
  DFunLike.congr_fun φ.moduleColimitMap_comp x

end CompatibleMap
end LocalModuleSystem
end Langlands.Algebra
