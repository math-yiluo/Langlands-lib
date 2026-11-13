import Langlands.Geometry.FormalGroup.DeligneDeterminantLattice
import Mathlib.Algebra.Category.ModuleCat.Stalk
import Mathlib.Topology.Sheaves.Functors
import Mathlib.LinearAlgebra.Quotient.Basic

/-! # The constant-locus and total residue-fibre conditions in Deligne's data -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.DeligneFormalSpace

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

section StructuralStalks

variable {S : Scheme.{u}} {M N : S.Modules}

/-- The actual additive stalk map of a structural-module morphism. -/
def structuralStalkAddMap (f : M ⟶ N) (x : S) :
    TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) M.val.presheaf x ⟶
      TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) N.val.presheaf x :=
  (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
    ((Scheme.Modules.toPresheaf S).map f)

/-- The structural module's actual stalk map is linear over the local ring. -/
def structuralStalkLinearMap (f : M ⟶ N) (x : S) :
    TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) M.val.presheaf x →ₗ[S.presheaf.stalk x]
      TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) N.val.presheaf x where
  toFun := structuralStalkAddMap f x
  map_add' := (structuralStalkAddMap f x).hom.map_add
  map_smul' a m := by
    obtain ⟨U, hxU, a, rfl⟩ := TopCat.Presheaf.exists_germ_eq S.presheaf a
    obtain ⟨V, hVU, hxV, m, rfl⟩ :=
      TopCat.Presheaf.exists_le_germ_eq M.val.presheaf m hxU
    rw [← TopCat.Presheaf.germ_res_apply S.presheaf (homOfLE hVU) x hxV a]
    let r : (S.ringCatSheaf.obj.obj (.op V)) :=
      S.presheaf.map (homOfLE hVU).op a
    let mV : M.val.obj (.op V) := m
    calc
      structuralStalkAddMap f x
          (S.presheaf.germ V x hxV r •
            TopCat.Presheaf.germ M.val.presheaf V x hxV mV) =
          structuralStalkAddMap f x
            (TopCat.Presheaf.germ M.val.presheaf V x hxV (r • mV)) :=
        congrArg (structuralStalkAddMap f x)
          (PresheafOfModules.germ_smul M.val x V hxV r mV).symm
      _ = TopCat.Presheaf.germ N.val.presheaf V x hxV
          (f.val.app (.op V) (r • mV)) :=
        TopCat.Presheaf.stalkFunctor_map_germ_apply V x hxV
          ((Scheme.Modules.toPresheaf S).map f) (r • mV)
      _ = TopCat.Presheaf.germ N.val.presheaf V x hxV
          (r • f.val.app (.op V) mV) :=
        congrArg (TopCat.Presheaf.germ N.val.presheaf V x hxV)
          ((f.val.app (.op V)).hom.map_smul r mV)
      _ = S.presheaf.germ V x hxV r •
          TopCat.Presheaf.germ N.val.presheaf V x hxV (f.val.app (.op V) mV) :=
        PresheafOfModules.germ_smul N.val x V hxV r (f.val.app (.op V) mV)
      _ = _ := congrArg (fun z => S.presheaf.germ V x hxV r • z)
        (TopCat.Presheaf.stalkFunctor_map_germ_apply V x hxV
          ((Scheme.Modules.toPresheaf S).map f) mV).symm

end StructuralStalks

/-- Forgetting scalar structure commutes with the actual stalk colimit. -/
def additiveStalkIso {O : Type u} [CommRing O] {X : TopCat.{u}}
    (M : X.Sheaf (ModuleCat.{u} O)) (x : X) :
    TopCat.Presheaf.stalk
        (M.obj ⋙ forget₂ (ModuleCat.{u} O) AddCommGrpCat.{u}) x ≅
      (forget₂ (ModuleCat.{u} O) AddCommGrpCat.{u}).obj
        (TopCat.Presheaf.stalk M.obj x) :=
  (preservesColimitIso (forget₂ (ModuleCat.{u} O) AddCommGrpCat.{u})
    ((OpenNhds.inclusion x).op ⋙ M.obj)).symm

/-- The additive stalk comparison sends a section's actual germ to the same germ. -/
theorem additiveStalkIso_inv_germ {O : Type u} [CommRing O] {X : TopCat.{u}}
    (M : X.Sheaf (ModuleCat.{u} O)) (U : Opens X) (x : X) (hx : x ∈ U) :
    (forget₂ (ModuleCat.{u} O) AddCommGrpCat.{u}).map
        (TopCat.Presheaf.germ M.obj U x hx) ≫ (additiveStalkIso M x).inv =
      TopCat.Presheaf.germ
        (M.obj ⋙ forget₂ (ModuleCat.{u} O) AddCommGrpCat.{u}) U x hx :=
  ι_preservesColimitIso_hom
    (forget₂ (ModuleCat.{u} O) AddCommGrpCat.{u})
    ((OpenNhds.inclusion x).op ⋙ M.obj) (.op ⟨U, hx⟩)

variable {O : Type u} [CommRing O] {d : ℕ} [NeZero d] {π : O}
  {F : Type u} [Field F] [Algebra O F] {S : Scheme.{u}}
  {φ : O →+* Γ(S, ⊤)}

namespace SheafPreDatum

variable (D : SheafPreDatum d π F φ)

/-- The actual subspace S_i of the Pi-zero locus on the i-th tangent line. -/
def piZeroSpace (i : ZMod d) : TopCat.{u} :=
  TopCat.of (D.tangent.graded.piZeroLocus i)

/-- Inclusion of the actual zero-locus subspace into S. -/
def piZeroInclusion (i : ZMod d) : D.piZeroSpace i ⟶ (S : TopCat) :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

/-- The actual inverse image of eta^i on S_i. -/
def componentOnPiZeroLocus (i : ZMod d) :
    (D.piZeroSpace i).Sheaf (ModuleCat.{u} O) :=
  (TopCat.Sheaf.pullback (ModuleCat.{u} O) (D.piZeroInclusion i)).obj
    (D.eta.lattice.component i)

/-- Condition (a): eta^i on the actual S_i is constant with fibre O^d. -/
def ConstantOnPiZeroLoci : Prop :=
  ∀ i : ZMod d, Nonempty (D.componentOnPiZeroLocus i ≅
    (constantSheaf (Opens.grothendieckTopology (D.piZeroSpace i))
      (ModuleCat.{u} O)).obj (ModuleCat.of O (Fin d → O)))

/-- The actual total eta stalk, rather than a selected homogeneous component. -/
def etaStalk (x : S) : ModuleCat.{u} O :=
  TopCat.Presheaf.stalk
    (latticeScalarSheaf d π (S : TopCat) D.eta.lattice.sheaf).obj x

/-- The actual Pi operator on the integral total eta stalk. -/
def etaStalkPi (x : S) : Module.End O (D.etaStalk x) :=
  ((TopCat.Presheaf.stalkFunctor (ModuleCat.{u} O) x).map
    (latticePi d π (S : TopCat) D.eta.lattice.sheaf).hom).hom

/-- The actual total quotient eta_s / Pi eta_s. -/
abbrev etaPiQuotient (x : S) :=
  D.etaStalk x ⧸ LinearMap.range (D.etaStalkPi x)

/-- The actual total tangent stalk, carrying its local-ring module structure. -/
def tangentStalk (x : S) : AddCommGrpCat.{u} :=
  TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) D.tangent.graded.module.val.presheaf x

instance tangentStalkModule (x : S) : Module (S.presheaf.stalk x) (D.tangentStalk x) :=
  inferInstanceAs (Module (S.presheaf.stalk x)
    (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
      D.tangent.graded.module.val.presheaf x))

/-- The additive map on total stalks induced by the actual sheaf map u. -/
def uStalkAdd (x : S) : D.etaStalk x →+ D.tangentStalk x :=
  ((additiveStalkIso
      (latticeScalarSheaf d π (S : TopCat) D.eta.lattice.sheaf) x).inv ≫
    (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      (Functor.whiskerRight D.u.hom
        (forget₂ (ModuleCat.{u} O) AddCommGrpCat.{u}))).hom

/-- On an actual germ, the stalk map u is the germ of its given section map. -/
theorem uStalkAdd_germ (U : S.Opens) (x : S) (hx : x ∈ U)
    (e : (latticeScalarSheaf d π (S : TopCat)
      D.eta.lattice.sheaf).obj.obj (.op U)) :
    D.uStalkAdd x
        (TopCat.Presheaf.germ
          (latticeScalarSheaf d π (S : TopCat) D.eta.lattice.sheaf).obj U x hx e) =
      TopCat.Presheaf.germ D.tangent.graded.module.val.presheaf U x hx
        (D.u.hom.app (.op U) e) := by
  have h := congrArg (fun f => f ≫
    (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      (Functor.whiskerRight D.u.hom
        (forget₂ (ModuleCat.{u} O) AddCommGrpCat.{u})))
    (additiveStalkIso_inv_germ
      (latticeScalarSheaf d π (S : TopCat) D.eta.lattice.sheaf) U x hx)
  rw [TopCat.Presheaf.stalkFunctor_map_germ] at h
  exact congrArg (fun f => f e) h

/-- The actual local-ring-linear Pi operator on the total tangent stalk. -/
def tangentStalkPi (x : S) : Module.End (S.presheaf.stalk x) (D.tangentStalk x) :=
  structuralStalkLinearMap D.tangent.graded.pi x

/-- The actual total u map commutes with the actual Pi operators on stalks. -/
theorem uStalkAdd_pi (x : S) (e : D.etaStalk x) :
    D.uStalkAdd x (D.etaStalkPi x e) =
      D.tangentStalkPi x (D.uStalkAdd x e) := by
  obtain ⟨U, hx, e, rfl⟩ := TopCat.Presheaf.exists_germ_eq
    (latticeScalarSheaf d π (S : TopCat) D.eta.lattice.sheaf).obj e
  let eV : D.eta.lattice.sheaf.obj.obj (.op U) := e
  calc
    D.uStalkAdd x (D.etaStalkPi x
        (TopCat.Presheaf.germ
          (latticeScalarSheaf d π (S : TopCat) D.eta.lattice.sheaf).obj U x hx e)) =
      D.uStalkAdd x (TopCat.Presheaf.germ
        (latticeScalarSheaf d π (S : TopCat) D.eta.lattice.sheaf).obj U x hx
        (PiAlgebra.pi d π • eV)) :=
      congrArg (D.uStalkAdd x)
        (TopCat.Presheaf.stalkFunctor_map_germ_apply U x hx
          (latticePi d π (S : TopCat) D.eta.lattice.sheaf).hom e)
    _ = TopCat.Presheaf.germ D.tangent.graded.module.val.presheaf U x hx
        (D.u.hom.app (.op U) (PiAlgebra.pi d π • eV)) :=
      D.uStalkAdd_germ U x hx (PiAlgebra.pi d π • eV)
    _ = TopCat.Presheaf.germ D.tangent.graded.module.val.presheaf U x hx
        (D.tangent.graded.pi.val.app (.op U) (D.u.hom.app (.op U) e)) :=
      congrArg (TopCat.Presheaf.germ D.tangent.graded.module.val.presheaf U x hx)
        (D.u_pi_apply U e)
    _ = D.tangentStalkPi x
        (TopCat.Presheaf.germ D.tangent.graded.module.val.presheaf U x hx
          (D.u.hom.app (.op U) e)) :=
      (TopCat.Presheaf.stalkFunctor_map_germ_apply U x hx
        ((Scheme.Modules.toPresheaf S).map D.tangent.graded.pi)
        (D.u.hom.app (.op U) e)).symm
    _ = _ := congrArg (D.tangentStalkPi x) (D.uStalkAdd_germ U x hx e).symm

/-- The actual local-ring module T_s / Pi T_s. -/
abbrev tangentPiQuotient (x : S) :=
  D.tangentStalk x ⧸ LinearMap.range (D.tangentStalkPi x)

/-- The actual residue-field extension of the total tangent Pi quotient. -/
def tangentPiQuotientFibre (x : S) : ModuleCat.{u} (S.residueField x) :=
  (ModuleCat.extendScalars (S.residue x).hom).obj
    (ModuleCat.of (S.presheaf.stalk x) (D.tangentPiQuotient x))

/-- Quotient by the actual tangent Pi image, then the actual residue-field unit. -/
def tangentPiFibreMap (x : S) : D.tangentStalk x →+ D.tangentPiQuotientFibre x :=
  (((ModuleCat.extendRestrictScalarsAdj (S.residue x).hom).unit.app
    (ModuleCat.of (S.presheaf.stalk x) (D.tangentPiQuotient x))).hom.toAddMonoidHom).comp
      (LinearMap.range (D.tangentStalkPi x)).mkQ.toAddMonoidHom

/-- The constructed tangent-to-fibre map annihilates the Pi image. -/
theorem tangentPiFibreMap_pi (x : S) (t : D.tangentStalk x) :
    D.tangentPiFibreMap x (D.tangentStalkPi x t) = 0 := by
  have h : (LinearMap.range (D.tangentStalkPi x)).mkQ (D.tangentStalkPi x t) = 0 :=
    (Submodule.Quotient.mk_eq_zero _).mpr ⟨t, rfl⟩
  change ((ModuleCat.extendRestrictScalarsAdj (S.residue x).hom).unit.app
    (ModuleCat.of (S.presheaf.stalk x) (D.tangentPiQuotient x)))
      ((LinearMap.range (D.tangentStalkPi x)).mkQ (D.tangentStalkPi x t)) = 0
  rw [h]
  exact map_zero _

/-- The total integral eta stalk maps into the actual tangent quotient fibre through u. -/
def uResidueFibreMap (x : S) : D.etaStalk x →+ D.tangentPiQuotientFibre x :=
  (D.tangentPiFibreMap x).comp (D.uStalkAdd x)

/-- The map induced by u annihilates the source Pi image, so it descends. -/
theorem etaPiRange_le_residueKernel (x : S) :
    (LinearMap.range (D.etaStalkPi x)).toAddSubgroup ≤ (D.uResidueFibreMap x).ker := by
  rintro e ⟨v, rfl⟩
  change D.tangentPiFibreMap x (D.uStalkAdd x (D.etaStalkPi x v)) = 0
  rw [D.uStalkAdd_pi]
  exact D.tangentPiFibreMap_pi x _

/-- The actual map of condition (b), descended from total u through total Pi quotients. -/
def piQuotientResidueMap (x : S) :
    D.etaPiQuotient x →+ D.tangentPiQuotientFibre x :=
  QuotientAddGroup.lift (LinearMap.range (D.etaStalkPi x)).toAddSubgroup
    (D.uResidueFibreMap x) (D.etaPiRange_le_residueKernel x)

/-- The descended map is the original u-to-fibre map on each quotient representative. -/
theorem piQuotientResidueMap_mk (x : S) (e : D.etaStalk x) :
    D.piQuotientResidueMap x ((LinearMap.range (D.etaStalkPi x)).mkQ e) =
      D.uResidueFibreMap x e :=
  QuotientAddGroup.lift_mk _ (D.etaPiRange_le_residueKernel x) e

/-- Condition (b): the actual total quotient-to-residue-fibre map is injective. -/
def ResidueFibreInjective : Prop :=
  ∀ x : S, Function.Injective (D.piQuotientResidueMap x)

/-- All three constructed admissibility conditions, with stalkwise determinant normalization. -/
def Admissible (hπ : algebraMap O F π ≠ 0) : Prop :=
  D.ConstantOnPiZeroLoci ∧ D.ResidueFibreInjective ∧ D.DeterminantNormalized hπ

end SheafPreDatum

end Langlands.DeligneFormalSpace
