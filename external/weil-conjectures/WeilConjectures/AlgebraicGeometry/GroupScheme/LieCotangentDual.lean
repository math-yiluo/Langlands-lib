/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.Lie.Ring
public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.LinearAlgebra.Dual.Defs
public import WeilConjectures.AlgebraicGeometry.RationalPointTangentDerivationIdentification
public import WeilConjectures.AlgebraicGeometry.GroupScheme.LieCotangentDualResidue
public import WeilConjectures.AlgebraicGeometry.GroupScheme.LieIdentityTangentEquiv

/-!
# The Lie algebra and the cotangent dual at the identity

Source: blueprint `proposition-cartier-s-theorem`, third paragraph, and the dimension paragraph of
`lemma-connected-components-images-homomorphisms--3`.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory
open scoped MonObj

namespace AlgebraicGeometry.GrpObj

/-- Restricting scalars along a ring isomorphism `r : k ≃+* K` identifies `k`-linear forms with
`K`-linear forms, semilinearly along `r`: transport the values by `r`. -/
noncomputable def cotangentDualScalarEquiv
    {k K : Type u} [Field k] [Field K] (r : k ≃+* K)
    (M : Type u) [AddCommGroup M] [Module K M] :
    letI : RingHomInvPair r.toRingHom r.symm.toRingHom :=
      RingHomInvPair.of_ringEquiv r
    letI : RingHomInvPair r.symm.toRingHom r.toRingHom :=
      RingHomInvPair.of_ringEquiv r.symm
    letI : Module k M := Module.compHom M r.toRingHom
    (M →ₗ[k] k) ≃ₛₗ[r.toRingHom] (M →ₗ[K] K) := by
  letI : RingHomInvPair r.toRingHom r.symm.toRingHom :=
    RingHomInvPair.of_ringEquiv r
  letI : RingHomInvPair r.symm.toRingHom r.toRingHom :=
    RingHomInvPair.of_ringEquiv r.symm
  letI : Module k M := Module.compHom M r.toRingHom
  let f : (M →ₗ[k] k) →ₛₗ[r.toRingHom] (M →ₗ[K] K) :=
    { toFun := fun φ ↦
        { toFun := fun m ↦ r (φ m)
          map_add' := by intros; simp
          map_smul' := by
            intro c m
            have h := φ.map_smul (r.symm c) m
            change φ (r (r.symm c) • m) = r.symm c * φ m at h
            rw [r.apply_symm_apply] at h
            rw [h, map_mul, r.apply_symm_apply]
            rfl }
      map_add' := by intros; ext; simp
      map_smul' := by intros; ext; simp }
  apply LinearEquiv.ofBijective f
  constructor
  · intro φ ψ h
    ext m
    exact r.injective (congrArg (fun L : M →ₗ[K] K ↦ L m) h)
  · intro ψ
    let φ : M →ₗ[k] k :=
      { toFun := fun m ↦ r.symm (ψ m)
        map_add' := by intros; simp
        map_smul' := by
          intro c m
          change r.symm (ψ (r c • m)) = c * r.symm (ψ m)
          rw [ψ.map_smul, smul_eq_mul, map_mul, r.symm_apply_apply] }
    exact ⟨φ, by ext m; exact r.apply_symm_apply (ψ m)⟩

/-- The structural residue map `k → κ(e)` at the identity `e` of `G` is a ring isomorphism,
since `e` is a rational point (`identity_residue_rational`). -/
def identityResidueEquiv {k : Type u} [Field k] (G : Over (Spec (.of k))) [GrpObj G] :
    k ≃+* IsLocalRing.ResidueField
      (G.left.presheaf.stalk (unitSection G (IsLocalRing.closedPoint k))) :=
  RingEquiv.ofBijective _ (identity_residue_rational G).1

/-- The defining formula of `identityResidueEquiv`. -/
theorem identityResidueEquiv_apply {k : Type u} [Field k] (G : Over (Spec (.of k)))
    [GrpObj G] (c : k) :
    let x := unitSection G (IsLocalRing.closedPoint k)
    identityResidueEquiv G c =
      (StructureSheaf.toStalk k (G.hom x) ≫ G.hom.stalkMap x ≫ G.left.residue x).hom c :=
  rfl

/-- The Lie algebra is the dual of the cotangent space at the rational identity, with
scalars transported by the residue-field identification `identityResidueEquiv`. No smoothness
is required. It is the composite of `lieIdentityTangentEquiv`, the rational
tangent-cotangent duality `exists_rationalPoint_tangent_cotangent_linearEquiv` (the
epsilon coefficient of the induced stalk map), and transport of the values of a functional
along `identityResidueEquiv`. Its defining formula is
`lieCotangentDualEquiv_apply_toCotangent`.

Source: blueprint `proposition-cartier-s-theorem`, third paragraph, and
`lemma-connected-components-images-homomorphisms--3`, dimension paragraph; Stacks Project, Tag
0B2C. -/
def lieCotangentDualEquiv {k : Type u} [Field k] (G : Over (Spec (.of k))) [GrpObj G] :
    let R := G.left.presheaf.stalk (unitSection G (IsLocalRing.closedPoint k))
    letI : RingHomInvPair (identityResidueEquiv G).toRingHom
        (identityResidueEquiv G).symm.toRingHom :=
      ⟨(identityResidueEquiv G).symm_toRingHom_comp_toRingHom,
        (identityResidueEquiv G).symm.symm_toRingHom_comp_toRingHom⟩
    letI : RingHomInvPair (identityResidueEquiv G).symm.toRingHom
        (identityResidueEquiv G).toRingHom :=
      ⟨(identityResidueEquiv G).symm.symm_toRingHom_comp_toRingHom,
        (identityResidueEquiv G).symm_toRingHom_comp_toRingHom⟩
    Lie G ≃ₛₗ[(identityResidueEquiv G).toRingHom]
      Module.Dual (IsLocalRing.ResidueField R) (IsLocalRing.CotangentSpace R) := by
  let x := unitSection G (IsLocalRing.closedPoint k)
  let R := G.left.presheaf.stalk x
  let K := G.left.residueField x
  let ρ : k →+* K :=
    (StructureSheaf.toStalk k (G.hom x) ≫ G.hom.stalkMap x ≫ G.left.residue x).hom
  let r := identityResidueEquiv G
  let : RingHomInvPair r.toRingHom r.symm.toRingHom :=
    RingHomInvPair.of_ringEquiv r
  let : RingHomInvPair r.symm.toRingHom r.toRingHom :=
    RingHomInvPair.of_ringEquiv r.symm
  let : Module k (schemeTangentSpace k G.left G.hom x) :=
    Module.compHom (schemeTangentSpace k G.left G.hom x) ρ
  exact ((lieIdentityTangentEquiv G).trans
    (exists_rationalPoint_tangent_cotangent_linearEquiv k G.left G.hom x
      (identity_residue_rational G).1).choose).trans (cotangentDualScalarEquiv r _)

/-- The defining formula of `lieCotangentDualEquiv`: the functional attached to `v` sends the
class of `a` in `m/m²` to the epsilon coefficient of `θ^♯ a`, where `θ` is the tangent vector
`lieIdentityTangentEquiv G v` and `θ^♯` its stalk map into the dual numbers over `κ(e)`. -/
theorem lieCotangentDualEquiv_apply_toCotangent
    {k : Type u} [Field k] (G : Over (Spec (.of k))) [GrpObj G] (v : Lie G) :
    let x := unitSection G (IsLocalRing.closedPoint k)
    let R := G.left.presheaf.stalk x
    let θ := lieIdentityTangentEquiv G v
    ∃ hx : θ.val (IsLocalRing.closedPoint (DualNumber (G.left.residueField x))) = x,
      ∀ a : IsLocalRing.maximalIdeal R,
        lieCotangentDualEquiv G v ((IsLocalRing.maximalIdeal R).toCotangent a) =
          TrivSqZeroExt.snd ((eqToHom (congrArg (fun y : G.left ↦ G.left.presheaf.stalk y)
            hx.symm) ≫ Scheme.stalkClosedPointTo θ.val).hom a) := by
  let x := unitSection G (IsLocalRing.closedPoint k)
  let R := G.left.presheaf.stalk x
  let K := G.left.residueField x
  let ρ : k →+* K :=
    (StructureSheaf.toStalk k (G.hom x) ≫ G.hom.stalkMap x ≫ G.left.residue x).hom
  let : Module k (schemeTangentSpace k G.left G.hom x) :=
    Module.compHom (schemeTangentSpace k G.left G.hom x) ρ
  have hF := (exists_rationalPoint_tangent_cotangent_linearEquiv k G.left G.hom x
    (identity_residue_rational G).1).choose_spec
  obtain ⟨hx, D, ⟨hD, hDm⟩, -⟩ := hF (lieIdentityTangentEquiv G v)
  refine ⟨hx, fun a ↦ ?_⟩
  have h := congrArg TrivSqZeroExt.snd (hD a)
  simp only [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr,
    zero_add] at h
  rw [h, ← hDm a]
  rfl

end AlgebraicGeometry.GrpObj
