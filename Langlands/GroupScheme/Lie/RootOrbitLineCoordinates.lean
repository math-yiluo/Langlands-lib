import Langlands.GroupScheme.Lie.SplitRootWeightGaloisCoordinates
import Langlands.Algebra.FiniteGaloisOrbitCoordinates

/-! # Coherent linear coordinates on actual Galois root orbits -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

universe u v w

namespace Langlands.LinearAlgebra.OrbitLines

section Transport

variable {Γ : Type u} [Group Γ] {I : Type v} [MulAction Γ I]
    {V : Type w} [MulAction Γ V] (i : I) (b : V)
    (hfixed : ∀ σ : MulAction.stabilizer Γ i, (σ : Γ) • b = b)

/-- A choice of transporter for a point of a single orbit. -/
def transporter (j : MulAction.orbit Γ i) : Γ :=
  Classical.choose (MulAction.mem_orbit_iff.mp j.property)

theorem transporter_spec (j : MulAction.orbit Γ i) :
    transporter i j • i = j.val :=
  Classical.choose_spec (MulAction.mem_orbit_iff.mp j.property)

/-- Transport a stabilizer-fixed vector across the orbit. -/
def basisVector (j : MulAction.orbit Γ i) : V :=
  transporter i j • b

include hfixed in
/-- The transported vector is independent of the transporter. -/
theorem basisVector_eq_smul (j : MulAction.orbit Γ i) (σ : Γ)
    (hσ : σ • i = j.val) :
    basisVector i b j = σ • b := by
  let τ := transporter i j
  have hτ : τ • i = j.val := transporter_spec i j
  have hs : τ⁻¹ * σ ∈ MulAction.stabilizer Γ i := by
    rw [MulAction.mem_stabilizer_iff, mul_smul, hσ, ← hτ, inv_smul_smul]
  change τ • b = σ • b
  calc
    τ • b = τ • ((τ⁻¹ * σ) • b) :=
      congrArg (fun x : V => τ • x) (hfixed ⟨τ⁻¹ * σ, hs⟩).symm
    _ = σ • b := by rw [smul_smul, mul_inv_cancel_left]

include hfixed in
/-- Orbit transport is equivariant for the original ambient action. -/
theorem basisVector_smul (σ : Γ) (j : MulAction.orbit Γ i) :
    basisVector i b (σ • j) = σ • basisVector i b j := by
  have hσ : (σ * transporter i j) • i = (σ • j).val := by
    rw [mul_smul, transporter_spec]
    rfl
  rw [basisVector_eq_smul i b hfixed (σ • j) _ hσ, mul_smul]
  rfl

end Transport

section Coordinates

variable {k L : Type u} [Field k] [Field L] [Algebra k L]
    {I : Type v} [MulAction (L ≃ₐ[k] L) I]
    {V : Type w} [AddCommGroup V] [Module L V]
    [DistribMulAction (L ≃ₐ[k] L) V] [SMulDistribClass (L ≃ₐ[k] L) L V]
    (i : I) (b : V)
    (hfixed : ∀ σ : MulAction.stabilizer (L ≃ₐ[k] L) i, (σ : L ≃ₐ[k] L) • b = b)
    (W : I → Submodule L V)
    (hW : ∀ (σ : L ≃ₐ[k] L) (j : I) {x : V}, x ∈ W j → σ • x ∈ W (σ • j))
    (hb : b ∈ W i) (hb0 : b ≠ 0)
    (hdim : ∀ j : MulAction.orbit (L ≃ₐ[k] L) i, Module.finrank L (W j.val) = 1)

include hW hb in
omit [SMulDistribClass (L ≃ₐ[k] L) L V] in
theorem basisVector_mem (j : MulAction.orbit (L ≃ₐ[k] L) i) :
    basisVector i b j ∈ W j.val := by
  have h := hW (transporter i j) i hb
  rwa [transporter_spec] at h

include hb0 in
omit [Module L V] [SMulDistribClass (L ≃ₐ[k] L) L V] in
theorem basisVector_ne_zero (j : MulAction.orbit (L ≃ₐ[k] L) i) :
    basisVector i b j ≠ 0 := by
  intro hz
  exact hb0 ((smul_eq_zero_iff_eq (transporter i j)).mp hz)

/-- Scalar coordinates on each line, using one coherently transported basis. -/
def linearEquiv (j : MulAction.orbit (L ≃ₐ[k] L) i) :
    L ≃ₗ[L] W j.val := by
  let vj : W j.val := ⟨basisVector i b j, basisVector_mem i b W hW hb j⟩
  have hvj : vj ≠ 0 := fun h => basisVector_ne_zero i b hb0 j (congrArg Subtype.val h)
  let f : L →ₗ[L] W j.val := (LinearMap.id : L →ₗ[L] L).smulRight vj
  exact LinearEquiv.ofBijective f
    ⟨fun _ _ h => smul_left_injective L hvj h,
      fun y => exists_smul_eq_of_finrank_eq_one (hdim j) hvj y⟩

omit [SMulDistribClass (L ≃ₐ[k] L) L V] in
theorem linearEquiv_apply_coe (j : MulAction.orbit (L ≃ₐ[k] L) i) (x : L) :
    (linearEquiv i b W hW hb hb0 hdim j x : V) = x • basisVector i b j := rfl

include hfixed in
/-- The same coordinate family intertwines every Galois transport, including
transport between distinct lines. -/
theorem linearEquiv_smul (σ : L ≃ₐ[k] L)
    (j : MulAction.orbit (L ≃ₐ[k] L) i) (x : L) :
    σ • (linearEquiv i b W hW hb hb0 hdim j x : V) =
      (linearEquiv i b W hW hb hb0 hdim (σ • j) (σ x) : V) := by
  rw [linearEquiv_apply_coe, linearEquiv_apply_coe,
    smul_distrib_smul, basisVector_smul i b hfixed]
  rfl

end Coordinates

end Langlands.LinearAlgebra.OrbitLines

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

variable (k L : Type u) [Field k] [Field L] [Algebra k L] [FiniteDimensional k L]
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    (j : T.toGrp ⟶ G)

local notation "b" => algebraBaseMap k L
local notation "j_L" => CategoryTheory.Functor.map (GroupScheme.baseChange b) j
local notation "T_L" => CategoryTheory.Functor.obj (CommGroupScheme.baseChange b) T
local notation "G_L" => CategoryTheory.Functor.obj (GroupScheme.baseChange b) G

local instance : IsAffineHom (G_L).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom b)
  infer_instance

attribute [local instance] rootsGaloisAction Lie.baseChangeGaloisAction

private def rootOrbitBaseVector
    (hG : IsConnectedReductive G) (hj : IsMaximalTorus j)
    (hT : IsSplitTorus ((CommGroupScheme.baseChange (algebraBaseMap k L)).obj T).toGrp)
    (β : roots
      (T := (CommGroupScheme.baseChange (algebraBaseMap k L)).obj T)
      (G := (GroupScheme.baseChange (algebraBaseMap k L)).obj G)
      ((GroupScheme.baseChange (algebraBaseMap k L)).map j)) : Additive (lieKernel G_L L) :=
  (splitRootWeightEquivariantLinearEquiv k L j hG hj hT β 1).val

private theorem rootOrbitBaseVector_fixed
    (hG : IsConnectedReductive G) (hj : IsMaximalTorus j)
    (hT : IsSplitTorus ((CommGroupScheme.baseChange (algebraBaseMap k L)).obj T).toGrp)
    (β : roots
      (T := (CommGroupScheme.baseChange (algebraBaseMap k L)).obj T)
      (G := (GroupScheme.baseChange (algebraBaseMap k L)).obj G)
      ((GroupScheme.baseChange (algebraBaseMap k L)).map j))
    (σ : MulAction.stabilizer (L ≃ₐ[k] L) β) :
    (σ : L ≃ₐ[k] L) • rootOrbitBaseVector k L j hG hj hT β =
      rootOrbitBaseVector k L j hG hj hT β := by
  change Lie.baseChangeGaloisEquiv k L G σ.val
    (splitRootWeightEquivariantLinearEquiv k L j hG hj hT β 1).val = _
  rw [splitRootWeightEquivariantLinearEquiv_galois, map_one]
  rfl

omit [FiniteDimensional k L] in
private theorem rootOrbit_weight_transport (σ : L ≃ₐ[k] L)
    (γ : roots (T := T_L) (G := G_L) j_L) {x : Additive (lieKernel G_L L)}
    (hx : x ∈ weightSpace (T := T_L) j_L γ.val) :
    σ • x ∈ weightSpace (T := T_L) j_L (σ • γ).val := by
  have hx' : x ∈ RelativeRoot.actionWeightSpace
      ((AutomorphicAction.conjugation j).baseChange b) γ.val := by
    rw [AutomorphicAction.baseChange_conjugation, RelativeRoot.actionWeightSpace_conjugation]
    exact hx
  have h := RelativeRoot.galois_mem_actionWeightSpace k L
    (AutomorphicAction.conjugation j) σ γ.val hx'
  rw [AutomorphicAction.baseChange_conjugation, RelativeRoot.actionWeightSpace_conjugation] at h
  exact h

/-- A single coordinate family on the actual Galois orbit of an actual split
maximal-torus root, with no supplied basis, action, or dimension premise. -/
def rootOrbitLineEquiv
    (hG : IsConnectedReductive G) (hj : IsMaximalTorus j)
    (hT : IsSplitTorus ((CommGroupScheme.baseChange (algebraBaseMap k L)).obj T).toGrp)
    (β : roots
      (T := (CommGroupScheme.baseChange (algebraBaseMap k L)).obj T)
      (G := (GroupScheme.baseChange (algebraBaseMap k L)).obj G)
      ((GroupScheme.baseChange (algebraBaseMap k L)).map j))
    (γ : MulAction.orbit (L ≃ₐ[k] L) β) :
    L ≃ₗ[L] weightSpace (T := T_L) j_L γ.val.val :=
  Langlands.LinearAlgebra.OrbitLines.linearEquiv
    (k := k) (L := L) (V := Additive (lieKernel G_L L)) β
    (rootOrbitBaseVector k L j hG hj hT β)
    (fun δ => weightSpace (T := T_L) j_L δ.val)
    (rootOrbit_weight_transport k L j)
    (splitRootWeightEquivariantLinearEquiv k L j hG hj hT β 1).property
    (by
      intro hz
      have hzero : splitRootWeightEquivariantLinearEquiv k L j hG hj hT β 1 = 0 :=
        Subtype.ext hz
      exact one_ne_zero
        ((splitRootWeightEquivariantLinearEquiv k L j hG hj hT β).map_eq_zero_iff.mp hzero))
    (fun δ => finrank_splitRootWeight_eq_one k L j hG hj hT δ.val) γ

/-- Every canonical coefficient transport respects the same coordinate
family, even when it moves the actual root. -/
theorem rootOrbitLineEquiv_galois
    (hG : IsConnectedReductive G) (hj : IsMaximalTorus j)
    (hT : IsSplitTorus ((CommGroupScheme.baseChange (algebraBaseMap k L)).obj T).toGrp)
    (β : roots
      (T := (CommGroupScheme.baseChange (algebraBaseMap k L)).obj T)
      (G := (GroupScheme.baseChange (algebraBaseMap k L)).obj G)
      ((GroupScheme.baseChange (algebraBaseMap k L)).map j))
    (σ : L ≃ₐ[k] L)
    (γ : MulAction.orbit (L ≃ₐ[k] L) β) (x : L) :
    Lie.baseChangeGaloisEquiv k L G σ (rootOrbitLineEquiv k L j hG hj hT β γ x).val =
      (rootOrbitLineEquiv k L j hG hj hT β (σ • γ) (σ x)).val := by
  let instAction : DistribMulAction (L ≃ₐ[k] L) (Additive (lieKernel G_L L)) :=
    Lie.baseChangeGaloisAction k L G
  let : SMul (L ≃ₐ[k] L) (Additive (lieKernel G_L L)) :=
    SemigroupAction.toSMul (self := MulAction.toSemigroupAction
      (self := DistribMulAction.toMulAction (self := instAction)))
  let : SMulDistribClass (L ≃ₐ[k] L) L (Additive (lieKernel G_L L)) :=
    ⟨fun σ c x => (Lie.baseChangeGaloisEquiv k L G σ).map_smulₛₗ c x⟩
  exact Langlands.LinearAlgebra.OrbitLines.linearEquiv_smul
    (k := k) (L := L) (V := Additive (lieKernel G_L L)) β
    (rootOrbitBaseVector k L j hG hj hT β)
    (rootOrbitBaseVector_fixed k L j hG hj hT β)
    (fun δ => weightSpace (T := T_L) j_L δ.val)
    (rootOrbit_weight_transport k L j) _ _ _ σ γ x

end Langlands.GroupScheme
