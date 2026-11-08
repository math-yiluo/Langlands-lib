import Langlands.GroupScheme.Rational.ModifiedProductImmersion
import Langlands.GroupScheme.Rational.CharpolyClassFunctions

/-! # Merged-root data for two adjacent simple roots -/

set_option backward.isDefEq.respectTransparency false

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SplitPinning

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    {p : SplitPinning G}

local instance : Mono p.inclusion.hom.hom.left := p.isMaximalTorus.2.1.mono

namespace RootParametrization

/-- A root map conjugated by a normalizer point `m`, as a root map of a root `r` whose root is
the Weyl translate by `m`. -/
def conjugate {α : p.rootIndex} (x : p.RootParametrization α) (m : normalizerPoints p.inclusion)
    {r : p.rootIndex}
    (hr : p.rootDatum.root r = weylAction p.inclusion m (p.rootDatum.root α)) :
    p.RootParametrization r where
  hom := x.conjugateHom m
  represents := by
    have h := x.represents.comp_iso (G.innerIso m)
    have hw : weylAction p.inclusion m⁻¹ (p.rootDatum.root r) = p.rootDatum.root α := by
      rw [hr, map_inv]
      exact (weylAction p.inclusion m).symm_apply_apply _
    have hc := RelativeRoot.subgroup_comap_innerIso p.inclusion (p.rootDatum.root r) m⁻¹
    rw [hw, show ((m⁻¹ : normalizerPoints p.inclusion) : Over.mk (𝟙 _) ⟶ G.X) =
      (m : Over.mk (𝟙 _) ⟶ G.X)⁻¹ from rfl, innerIso_inv_hom] at hc
    rw [← hc]
    exact h
  isClosedSubgroup := x.isClosedSubgroup_conjugateHom m
  torus_equivariant := by
    intro T t c
    have h := x.conjugateHom_torus_equivariant m T t c
    rw [AutomorphicAction.conjugation_act, ← hr] at h
    exact h

@[simp] theorem conjugate_hom {α : p.rootIndex} (x : p.RootParametrization α)
    (m : normalizerPoints p.inclusion) {r : p.rootIndex}
    (hr : p.rootDatum.root r = weylAction p.inclusion m (p.rootDatum.root α)) :
    (x.conjugate m hr).hom = x.conjugateHom m :=
  rfl

end RootParametrization

/-- A normalizer point acting on characters by the reflection of `α` is a reflection
representative of `α`. -/
def ReflectionRepresentative.ofNormalizerPoint {α : p.rootIndex}
    (m : normalizerPoints p.inclusion)
    (hm : weylAction p.inclusion m = p.rootDatum.reflection α) : p.ReflectionRepresentative α where
  point := m
  torusAut := normalizingAut p.inclusion m
  normalizes := isNormalizingPoint_normalizingAut p.inclusion m
  characterAut_eq := hm

@[simp] theorem ReflectionRepresentative.ofNormalizerPoint_point {α : p.rootIndex}
    (m : normalizerPoints p.inclusion)
    (hm : weylAction p.inclusion m = p.rootDatum.reflection α) :
    (ReflectionRepresentative.ofNormalizerPoint m hm).point = m :=
  rfl

section Adjacent

variable (a b : p.base.support)

/-- If `⟨b, a^∨⟩ = -1`, the reflection of `b` in `a` is the root `a + b`. -/
theorem root_reflectionPerm_of_pairing_eq_neg_one
    (h : p.rootDatum.pairing (b : p.rootIndex) (a : p.rootIndex) = -1) :
    p.rootDatum.root (p.rootDatum.reflectionPerm (a : p.rootIndex) (b : p.rootIndex)) =
      p.rootDatum.root (a : p.rootIndex) + p.rootDatum.root (b : p.rootIndex) := by
  rw [RootPairing.root_reflectionPerm, RootPairing.reflection_apply_root, h, neg_one_smul,
    sub_neg_eq_add, add_comm]

/-- The representative `n_a n_b n_a⁻¹` acts on characters by the reflection of `s_a(b)`. -/
theorem weylAction_conj_normalizerPoint (na : p.SimpleReflectionRepresentative a)
    (nb : p.SimpleReflectionRepresentative b) :
    weylAction p.inclusion (na.normalizerPoint * nb.normalizerPoint * na.normalizerPoint⁻¹) =
      p.rootDatum.reflection
        (p.rootDatum.reflectionPerm (a : p.rootIndex) (b : p.rootIndex)) := by
  rw [map_mul, map_mul, map_inv, na.weylAction_normalizerPoint, nb.weylAction_normalizerPoint,
    RootPairing.reflection_inv, RootPairing.reflection_reflectionPerm]

/-- **Merged-root data for adjacent simple roots.** For distinct simple roots `a`, `b` with
`⟨b, a^∨⟩ = -1`, the merged root is `s_a(b) = a + b`. Its root map is the root map of `b`
conjugated by `n_a`, and its representative is `n_a n_b n_a⁻¹`. -/
def adjacentModifiedData (hab : a ≠ b)
    (h : p.rootDatum.pairing (b : p.rootIndex) (a : p.rootIndex) = -1)
    (xb : p.NormalizedRootParametrization b) (na : p.SimpleReflectionRepresentative a)
    (nb : p.SimpleReflectionRepresentative b) (ca cb : k) (hca : ca ≠ 0) (hcb : cb ≠ 0) :
    p.SteinbergModifiedData where
  a := a
  b := b
  a_ne_b := hab
  alpha := p.rootDatum.reflectionPerm (a : p.rootIndex) (b : p.rootIndex)
  root_eq := root_reflectionPerm_of_pairing_eq_neg_one a b h
  xAlpha := xb.toRootParametrization.conjugate na.normalizerPoint (by
    rw [RootPairing.root_reflectionPerm, na.weylAction_normalizerPoint])
  nAlpha := ReflectionRepresentative.ofNormalizerPoint
    (na.normalizerPoint * nb.normalizerPoint * na.normalizerPoint⁻¹)
    (weylAction_conj_normalizerPoint a b na nb)
  ca := ca
  cb := cb
  ca_ne_zero := hca
  cb_ne_zero := hcb

variable {a b} {hab : a ≠ b}
    {h : p.rootDatum.pairing (b : p.rootIndex) (a : p.rootIndex) = -1}
    {xb : p.NormalizedRootParametrization b} {na : p.SimpleReflectionRepresentative a}
    {nb : p.SimpleReflectionRepresentative b} {ca cb : k} {hca : ca ≠ 0} {hcb : cb ≠ 0}

/-- If `n_b` is generated by the rational root subgroups of `±b`, the merged representative
`n_a n_b n_a⁻¹` is generated by those of `±(a + b)`. -/
theorem adjacentModifiedData_nAlpha_mem
    (hnb : nb.point ∈
      (RelativeRoot.subgroup p.inclusion (p.rootDatum.root (b : p.rootIndex))).carrier
          (Over.mk (𝟙 _)) ⊔
        (RelativeRoot.subgroup p.inclusion (-p.rootDatum.root (b : p.rootIndex))).carrier
          (Over.mk (𝟙 _))) :
    (adjacentModifiedData a b hab h xb na nb ca cb hca hcb).nAlpha.point ∈
      (RelativeRoot.subgroup p.inclusion
          (p.rootDatum.root (adjacentModifiedData a b hab h xb na nb ca cb hca hcb).alpha)).carrier
          (Over.mk (𝟙 _)) ⊔
        (RelativeRoot.subgroup p.inclusion
          (-p.rootDatum.root (adjacentModifiedData a b hab h xb na nb ca cb hca hcb).alpha)).carrier
          (Over.mk (𝟙 _)) := by
  let m := na.normalizerPoint
  have hconj (χ : characterLattice p.torus) (g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X)
      (hg : g ∈ (RelativeRoot.subgroup p.inclusion χ).carrier (Over.mk (𝟙 _))) :
      (m : Over.mk (𝟙 _) ⟶ G.X) * g * (m : Over.mk (𝟙 _) ⟶ G.X)⁻¹ ∈
        (RelativeRoot.subgroup p.inclusion (weylAction p.inclusion m χ)).carrier
          (Over.mk (𝟙 _)) := by
    have hm := RelativeRoot.normalizer_conj_mem p.inclusion χ m hg
    rwa [constantPoint_self] at hm
  have hw : weylAction p.inclusion m (p.rootDatum.root (b : p.rootIndex)) =
      p.rootDatum.root (p.rootDatum.reflectionPerm (a : p.rootIndex) (b : p.rootIndex)) := by
    rw [RootPairing.root_reflectionPerm, na.weylAction_normalizerPoint]
  let φ := (MulAut.conj (m : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X)).toMonoidHom
  have hle : ((RelativeRoot.subgroup p.inclusion (p.rootDatum.root (b : p.rootIndex))).carrier
        (Over.mk (𝟙 _)) ⊔
      (RelativeRoot.subgroup p.inclusion (-p.rootDatum.root (b : p.rootIndex))).carrier
        (Over.mk (𝟙 _))).map φ ≤
      (RelativeRoot.subgroup p.inclusion
          (p.rootDatum.root (p.rootDatum.reflectionPerm (a : p.rootIndex)
            (b : p.rootIndex)))).carrier (Over.mk (𝟙 _)) ⊔
        (RelativeRoot.subgroup p.inclusion
          (-p.rootDatum.root (p.rootDatum.reflectionPerm (a : p.rootIndex)
            (b : p.rootIndex)))).carrier (Over.mk (𝟙 _)) := by
    rw [Subgroup.map_sup]
    refine sup_le_sup ?_ ?_
    · rintro _ ⟨g, hg, rfl⟩
      have hg' := hconj _ g hg
      rwa [hw] at hg'
    · rintro _ ⟨g, hg, rfl⟩
      have hg' := hconj _ g hg
      rwa [map_neg, hw] at hg'
  exact hle ⟨nb.point, hnb, rfl⟩

end Adjacent

section Path

open MatrixRepresentation Langlands.LinearAlgebra.RootDatumPathWeights

variable {d : Type} [Fintype d] [DecidableEq d] {ρ : MatrixRepresentation G d}
  {L : ℕ} {β : Fin L → p.base.support} {lam : characterLattice p.torus}

/-- Consecutive vertices of a path component have pairing `-1`. -/
theorem pairing_path_succ (hβ : IsPathComponent β) {i : ℕ} (hi : i + 2 ≤ L) :
    p.rootDatum.pairing (β ⟨i + 1, by omega⟩ : p.rootIndex) (β ⟨i, by omega⟩ : p.rootIndex) =
      -1 := by
  rw [hβ.pairing_eq]
  simp

/-- Consecutive vertices of a path component are distinct. -/
theorem path_ne_succ (hβ : IsPathComponent β) {i : ℕ} (hi : i + 2 ≤ L) :
    β ⟨i, by omega⟩ ≠ β ⟨i + 1, by omega⟩ := by
  intro heq
  have h := pairing_path_succ hβ hi
  rw [← heq, RootPairing.pairing_same] at h
  norm_num at h

/-- The merged-root data of the consecutive path vertices `β i` and `β (i + 1)`, with the
supplied normalized root maps `x`, the canonical representative of `β (i + 1)`, an arbitrary
representative `na` of `β i` and nonzero scalars. -/
def pathAdjacentModifiedData (hβ : IsPathComponent β) {i : ℕ} (hi : i + 2 ≤ L)
    (x : p.NormalizedSimpleRootParametrizations)
    (na : p.SimpleReflectionRepresentative (β ⟨i, by omega⟩)) (ca cb : k) (hca : ca ≠ 0)
    (hcb : cb ≠ 0) : p.SteinbergModifiedData :=
  adjacentModifiedData _ _ (path_ne_succ hβ hi) (pairing_path_succ hβ hi) (x _) na
    (x _).reflectionRepresentative ca cb hca hcb

/-- **`f` vanishes on `N''` for the constructed data.** For a highest-weight representation at
the fundamental weight of the end of a path component, and the merged-root data of consecutive
path vertices built above, the restriction of the class function `det (1 - ρ)` along `N''` with
the canonical complementary representatives is zero. -/
theorem restriction_pathAdjacent_detOneSubClassFunction_eq_zero
    (hρ : p.IsHighestWeight ρ lam) (hβ : IsPathComponent β) (hlam : IsPathFundamental β lam)
    {i : ℕ} (hi : i + 2 ≤ L) (x : p.NormalizedSimpleRootParametrizations)
    (na : p.SimpleReflectionRepresentative (β ⟨i, by omega⟩)) (ca cb : k) (hca : ca ≠ 0)
    (hcb : cb ≠ 0) {q : ℕ}
    (e : Fin q ≃ (pathAdjacentModifiedData hβ hi x na ca cb hca hcb).Complement) :
    ClassFunctions.restriction G
        (steinbergModifiedProduct (pathAdjacentModifiedData hβ hi x na ca cb hca hcb) e x
          (canonicalSimpleReflectionRepresentatives x))
        (detOneSubClassFunction ρ) = 0 := by
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    ((representationWeightSpace_ne_bot_iff hρ hβ hlam
      (pathWeight β lam (i + 1))).mpr ⟨i + 1, by omega, rfl⟩)
  exact restriction_steinbergModifiedProduct_detOneSubClassFunction_eq_zero
    (pathAdjacentModifiedData hβ hi x na ca cb hca hcb) e x hρ hβ hlam hi
    rfl rfl (adjacentModifiedData_nAlpha_mem (x _).reflectionRepresentative_mem_generated) hv hv0

end Path

end Langlands.GroupScheme.SplitPinning
