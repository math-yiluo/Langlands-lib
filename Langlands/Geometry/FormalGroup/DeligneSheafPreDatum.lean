import Langlands.Geometry.FormalGroup.DeligneLatticeSheaf

/-! # The actual eta, T, u and r data before Deligne's admissibility conditions -/

noncomputable section

universe u

namespace Langlands.DeligneFormalSpace

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace

variable {O : Type u} [CommRing O] (S : Scheme.{u})

/-- The opposite of the top open is initial in the actual open-set category. -/
def opTopIsInitial : IsInitial (Opposite.op (⊤ : S.Opens)) :=
  IsInitial.ofUniqueHom (fun U => (homOfLE (show U.unop ≤ ⊤ from le_top)).op)
    (fun _ _ => Subsingleton.elim _ _)

set_option synthInstance.maxHeartbeats 100000 in
set_option backward.isDefEq.respectTransparency false in
/-- Forget structural scalars using their actual global-section homomorphism. -/
def structuralOSheafFunctor (φ : O →+* Γ(S, ⊤)) :
    S.Modules ⥤ (S : TopCat).Sheaf (ModuleCat.{u} O) :=
  let restriction : ModuleCat.{u} Γ(S, ⊤) ⥤ ModuleCat.{u} O :=
    ModuleCat.restrictScalars φ
  SheafOfModules.forgetToSheafModuleCat S.ringCatSheaf (Opposite.op ⊤) (opTopIsInitial S) ⋙
    sheafCompose (Opens.grothendieckTopology S) restriction

variable {S} (d : ℕ) [NeZero d] (π : O) (F : Type u) [Field F] [Algebra O F]
  (φ : O →+* Γ(S, ⊤))

/-- Deligne's four actual sheaf data, including the local generation requirement for u. -/
structure SheafPreDatum where
  eta : FramedLatticePiSheaf d π (S : TopCat) F
  tangent : LinePiSheaf d S (φ π)
  u : latticeScalarSheaf d π (S : TopCat) eta.lattice.sheaf ⟶
    (structuralOSheafFunctor S φ).obj tangent.graded.module
  uPi : latticePi d π (S : TopCat) eta.lattice.sheaf ≫ u =
    u ≫ (structuralOSheafFunctor S φ).map tangent.graded.pi
  uComponent (i : ZMod d) : eta.lattice.component i ⟶
    (structuralOSheafFunctor S φ).obj (tangent.graded.componentSheaf i)
  uComponent_inclusion (i : ZMod d) :
    uComponent i ≫ (structuralOSheafFunctor S φ).map (tangent.graded.componentInclusion i) =
      eta.lattice.inclusion i ≫ u
  locallyGenerates (U : S.Opens) (t : tangent.graded.module.val.obj (.op U))
      (x : S) (hx : x ∈ U) :
    ∃ (V : S.Opens) (hVU : V ≤ U), x ∈ V ∧
      tangent.graded.module.val.map (homOfLE hVU).op t ∈
        Submodule.span ((ringSheaf S.sheaf).obj.obj (.op V))
          (Set.range (fun e : (latticeScalarSheaf d π (S : TopCat)
              eta.lattice.sheaf).obj.obj (.op V) =>
            (show tangent.graded.module.val.obj (.op V) from u.hom.app (.op V) e)))

namespace SheafPreDatum

variable {d π F φ} (D : SheafPreDatum d π F φ)

/-- The actual underlying scalar map sends multiplication by Pi to the T-operator. -/
theorem u_pi_apply (U : S.Opens) (e : D.eta.lattice.sheaf.obj.obj (.op U)) :
    D.u.hom.app (.op U) (PiAlgebra.pi d π • e) =
      D.tangent.graded.pi.val.app (.op U) (D.u.hom.app (.op U) e) := by
  have h := congrArg (fun f => f.hom.app (.op U)) D.uPi
  exact congrArg (fun f => f e) h

/-- The selected homogeneous map is the restriction of the same total u. -/
theorem uComponent_inclusion_apply (i : ZMod d) (U : S.Opens)
    (e : (D.eta.lattice.component i).obj.obj (.op U)) :
    ((D.uComponent i).hom.app (.op U) e).val =
      D.u.hom.app (.op U) ((D.eta.lattice.inclusion i).hom.app (.op U) e) := by
  have h := congrArg (fun f => f.hom.app (.op U)) (D.uComponent_inclusion i)
  exact congrArg (fun f => f e) h

end SheafPreDatum

section AffineNilp

variable (B : FormalGroup.Nilp.{u, u} O π)

/-- The structural O-map into the actual global sections of Spec B. -/
def nilpGlobalScalar : O →+* Γ(Spec (CommRingCat.of B.obj), ⊤) :=
  ((Scheme.ΓSpecIso (CommRingCat.of B.obj)).inv.hom).comp (algebraMap O B.obj)

/-- Nilpotence is transported from the actual Nilp algebra, not added as separate data. -/
theorem nilpGlobalScalar_nilpotent : IsNilpotent (nilpGlobalScalar π B π) :=
  B.nilpotent.map (Scheme.ΓSpecIso (CommRingCat.of B.obj)).inv.hom

/-- The four sheaf data on an actual Nilp algebra, before conditions (a)-(c). -/
def NilpSheafPreDatum := SheafPreDatum d π F (nilpGlobalScalar π B)

end AffineNilp

end Langlands.DeligneFormalSpace
