import Langlands.GroupScheme.Rational.AdjacentSimpleRootCommutator
import Langlands.GroupScheme.Rational.PathMergedRootScalars
import Langlands.GroupScheme.Rational.SteinbergCanonicalGaloisTransport
import Langlands.GroupScheme.Rational.SteinbergRationalGaloisTransport
import Langlands.GroupScheme.Rational.CorootRationalGaloisTransport
import Langlands.GroupScheme.Rational.QuasiSplitCompatiblePinning
import Langlands.GroupScheme.Reductive.RootDatumGaloisCoroots
import Langlands.GroupScheme.Reductive.RootDatumTorusTransport
import Langlands.GroupScheme.Reductive.LocalWeylNormalizationStatement
import Langlands.GroupScheme.Reductive.PinnedRootFixedness
import Langlands.GroupScheme.Reductive.SplitPinnedOppositeFactorPairs

/-! # Galois-compatible merged-root data for adjacent simple roots -/

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option maxHeartbeats 400000

/-! ### A Galois twist on a set with an action of the automorphism group -/

section GaloisTwist

variable {k K : Type u} [Field k] [Field K] [Algebra k K] [FiniteDimensional k K]

/-- Dedekind's independence of characters: a combination of the automorphisms fixing a
point of a set, with nonzero coefficient at the identity, does not vanish identically. -/
theorem exists_stabilizer_sum_ne_zero {J : Type v} [MulAction (K ≃ₐ[k] K) J]
    [DecidableEq J] (f : (K ≃ₐ[k] K) → K) (hf : f 1 ≠ 0) (c : J) :
    ∃ z : K, (∑ g : K ≃ₐ[k] K, if g • c = c then f g * g z else 0) ≠ 0 := by
  have hli : LinearIndependent K (fun g : K ≃ₐ[k] K => (g : K → K)) :=
    (linearIndependent_monoidHom K K).comp (fun g : K ≃ₐ[k] K => (g : K →* K))
      (fun x y h => by ext z; exact DFunLike.congr_fun h z)
  by_contra! h
  have h0 := Fintype.linearIndependent_iff.mp hli (fun g => if g • c = c then f g else 0)
    (by
      funext z
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, ite_mul, zero_mul,
        Pi.zero_apply]
      exact h z)
  have h1 := h0 1
  simp only [one_smul, ↓reduceIte] at h1
  exact hf h1

/-- **Galois twist.** Let `φ` be a nonzero multiplicative cocycle of the automorphism group
with values in `K`, twisted by an action on a set `J`:
`φ (σ τ) c = σ (φ τ c) φ σ (τ c)`. Then there are nonzero scalars `mu c` with
`mu (σ c) = σ (mu c) φ σ c`. This is Hilbert's Theorem 90 for the stabilizers, spread over
the orbits. -/
theorem exists_galoisTwist {J : Type v} [MulAction (K ≃ₐ[k] K) J]
    (φ : (K ≃ₐ[k] K) → J → K) (hφ : ∀ σ c, φ σ c ≠ 0)
    (hcoc : ∀ σ τ c, φ (σ * τ) c = σ (φ τ c) * φ σ (τ • c)) :
    ∃ mu : J → K, (∀ c, mu c ≠ 0) ∧ ∀ σ c, mu (σ • c) = σ (mu c) * φ σ c := by
  classical
  obtain ⟨rep, hrep_smul, hrep_mem⟩ : ∃ rep : J → J,
      (∀ (σ : K ≃ₐ[k] K) c, rep (σ • c) = rep c) ∧
        ∀ c, ∃ g : K ≃ₐ[k] K, g • rep c = c := by
    refine ⟨fun c => (Quotient.mk (MulAction.orbitRel (K ≃ₐ[k] K) J) c).out,
      fun σ c => ?_, fun c => ?_⟩
    · exact congrArg Quotient.out (Quotient.sound (MulAction.mem_orbit c σ))
    · have h : (Quotient.mk (MulAction.orbitRel (K ≃ₐ[k] K) J) c).out ∈
          MulAction.orbit (K ≃ₐ[k] K) c :=
        Quotient.mk_out (s := MulAction.orbitRel (K ≃ₐ[k] K) J) c
      obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp h
      exact ⟨g⁻¹, inv_smul_eq_iff.mpr hg.symm⟩
  obtain ⟨z, hz_smul, hz⟩ : ∃ z : J → K, (∀ (σ : K ≃ₐ[k] K) c, z (σ • c) = z c) ∧
      ∀ c, (∑ g : K ≃ₐ[k] K,
        if g • rep c = rep c then φ g (rep c) * g (z c) else 0) ≠ 0 := by
    let zf : J → K := fun c₀ =>
      Classical.choose (exists_stabilizer_sum_ne_zero (fun g => φ g c₀) (hφ 1 c₀) c₀)
    refine ⟨fun c => zf (rep c), fun σ c => by simp only [hrep_smul], fun c => ?_⟩
    exact Classical.choose_spec
      (exists_stabilizer_sum_ne_zero (fun g => φ g (rep c)) (hφ 1 (rep c)) (rep c))
  set mu : J → K := fun c => ∑ g : K ≃ₐ[k] K,
    if g • rep c = c then φ g (rep c) * g (z c) else 0 with hmu
  have hlaw : ∀ σ c, mu (σ • c) = σ (mu c) * φ σ c := by
    intro σ c
    simp only [hmu, hrep_smul, hz_smul, map_sum, Finset.sum_mul]
    refine (Fintype.sum_equiv (Equiv.mulLeft σ) _ _ (fun g => ?_)).symm
    simp only [Equiv.coe_mulLeft]
    by_cases hg : g • rep c = c
    · have hσg : (σ * g) • rep c = σ • c := by rw [mul_smul, hg]
      rw [ite_eq_left hg, ite_eq_left hσg, hcoc, hg, map_mul, AlgEquiv.mul_apply]
      ring
    · have hσg : ¬ (σ * g) • rep c = σ • c := by
        rw [mul_smul]
        exact fun h => hg (smul_left_cancel σ h)
      rw [ite_eq_right hg, ite_eq_right hσg, map_zero, zero_mul]
  refine ⟨mu, fun c => ?_, hlaw⟩
  obtain ⟨g, hg⟩ := hrep_mem c
  have hrep_rep : rep (rep c) = rep c := by
    rw [← hrep_smul g (rep c), hg]
  have hz_rep : z (rep c) = z c := by
    rw [← hz_smul g (rep c), hg]
  have h0 : mu (rep c) ≠ 0 := by
    simp only [hmu, hrep_rep, hz_rep]
    exact hz c
  rw [← hg, hlaw]
  exact mul_ne_zero ((map_ne_zero g).mpr h0) (hφ g (rep c))

end GaloisTwist

namespace SplitPinning

/-! ### Rescaled root parametrizations -/

section Scale

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    {p : SplitPinning G}

namespace RootParametrization

/-- A root parametrization precomposed with multiplication by a unit `d`. -/
def scale {α : p.rootIndex} (x : p.RootParametrization α) (d : kˣ) :
    p.RootParametrization α where
  hom := LocalSplitCell.scaleHom (d : k) ≫ x.hom
  represents := by
    refine ⟨?_, ?_⟩
    · have : Mono x.hom.hom.hom := x.represents.1
      have : IsIso (LocalSplitCell.scaleHom (d : k)).hom.hom := inferInstance
      rw [Grp.comp_hom_hom]
      exact mono_comp _ _
    · rw [show LocalSplitCell.scaleHom (d : k) = (LocalSplitCell.scaleIso d).hom from rfl,
        SubgroupFunctor.range_iso_comp]
      exact x.represents.2
  isClosedSubgroup := by
    have : IsClosedImmersion x.hom.hom.hom.left := x.isClosedSubgroup
    have : IsIso (LocalSplitCell.scaleHom (d : k)).hom.hom.left :=
      inferInstanceAs (IsIso ((Over.forget _).map (LocalSplitCell.scaleHom (d : k)).hom.hom))
    change IsClosedImmersion ((LocalSplitCell.scaleHom (d : k)).hom.hom ≫ x.hom.hom.hom).left
    rw [Over.comp_left]
    infer_instance
  torus_equivariant T t c := by
    have e1 := LocalSplitCell.rootPoint_scaleHom (d : k) x.hom T c
    have e2 := LocalSplitCell.rootPoint_scaleHom (d : k) x.hom T
      (VectorGroup.charValue (p.rootDatum.root α) T t * c)
    simp only [LocalSplitCell.rootPoint] at e1 e2
    rw [e1, e2, x.torus_equivariant, mul_left_comm]

/-- The values of the rescaled map. -/
theorem scale_point {α : p.rootIndex} (x : p.RootParametrization α) (d : kˣ)
    (T : Over (Spec (CommRingCat.of k))) (c : Γ(T.left, ⊤)) :
    (x.scale d).point T c = x.point T (LocalSplitCell.baseScalar T (d : k) * c) :=
  LocalSplitCell.rootPoint_scaleHom (d : k) x.hom T c

/-- The rational values of the rescaled map. -/
theorem scale_rationalPoint {α : p.rootIndex} (x : p.RootParametrization α) (d : kˣ)
    (c : k) : (x.scale d).rationalPoint c = x.rationalPoint ((d : k) * c) := by
  rw [rationalPoint, scale_point, rationalPoint, map_mul]
  congr 2

end RootParametrization

end Scale

/-! ### Reflection representatives around a nonidentity root point -/

section RootPointRepresentative

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    (p : SplitPinning G)

local instance : IsClosedImmersion p.inclusion.hom.hom.left := p.isMaximalTorus.2.1

variable {α : p.rootIndex} {v : rationalPoints G}
    (hv : v ∈ (RelativeRoot.subgroup p.inclusion (p.rootDatum.root α)).carrier
      (Over.mk (𝟙 _))) (hv1 : v ≠ 1)

/-- The unique ordered opposite pair around a nonidentity rational point of a root
subgroup. -/
def rootPointOppositePair : rationalPoints G × rationalPoints G :=
  Classical.choose (splitPinnedOppositeFactorPairs k G p (p.rootDatum.root α)
    (p.root_mem_relativeRoots α) v hv hv1)

theorem rootPointOppositePair_spec :
    RelativeRoot.IsOppositeFactorPair p.inclusion (p.rootDatum.root α) v
      (p.rootPointOppositePair hv hv1) :=
  Classical.choose_spec (splitPinnedOppositeFactorPairs k G p (p.rootDatum.root α)
    (p.root_mem_relativeRoots α) v hv hv1)

/-- Every ordered opposite pair around the same point is the chosen pair. -/
theorem eq_rootPointOppositePair {q : rationalPoints G × rationalPoints G}
    (hq : RelativeRoot.IsOppositeFactorPair p.inclusion (p.rootDatum.root α) v q) :
    q = p.rootPointOppositePair hv hv1 :=
  hq.eq p.inclusion p.isSplitTorus (p.root_mem_relativeRoots α).1 hv hv1
    (p.rootPointOppositePair_spec hv hv1)

/-- The reflection representative `q₁ v q₂` of the root `α` determined by a nonidentity
rational point `v` of its root subgroup. -/
def rootPointReflectionRepresentative : p.ReflectionRepresentative α :=
  let n : normalizerPoints p.inclusion :=
    ⟨(p.rootPointOppositePair hv hv1).1 * v * (p.rootPointOppositePair hv hv1).2,
      (p.rootPointOppositePair_spec hv hv1).2.2⟩
  { point := n.val
    torusAut := normalizingAut p.inclusion n
    normalizes := isNormalizingPoint_normalizingAut p.inclusion n
    characterAut_eq := p.oppositeFactorPair_weylAction α hv hv1
      (p.rootPointOppositePair_spec hv hv1) }

theorem rootPointReflectionRepresentative_point :
    (p.rootPointReflectionRepresentative hv hv1).point =
      (p.rootPointOppositePair hv hv1).1 * v * (p.rootPointOppositePair hv hv1).2 :=
  rfl

/-- The representative is generated by the rational root subgroups of `± α`. -/
theorem rootPointReflectionRepresentative_mem_generated :
    (p.rootPointReflectionRepresentative hv hv1).point ∈
      (RelativeRoot.subgroup p.inclusion (p.rootDatum.root α)).carrier (Over.mk (𝟙 _)) ⊔
        (RelativeRoot.subgroup p.inclusion (-p.rootDatum.root α)).carrier
          (Over.mk (𝟙 _)) :=
  Subgroup.mul_mem _
    (Subgroup.mul_mem _
      (Subgroup.mem_sup_right (p.rootPointOppositePair_spec hv hv1).1)
      (Subgroup.mem_sup_left hv))
    (Subgroup.mem_sup_right (p.rootPointOppositePair_spec hv hv1).2.1)

end RootPointRepresentative

/-! ### Coefficient transport of these representatives -/

section Galois

open GaloisPointComparison

variable (k K : Type u) [Field k] [Field K] [Algebra k K]
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    (i : T.toGrp ⟶ G)

local instance mergedRootGaloisIsAffineHom :
    IsAffineHom ((GroupScheme.baseChange (algebraBaseMap k K)).obj G).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom (algebraBaseMap k K))
  infer_instance

variable (p : Langlands.GroupScheme.SplitPinning
    ((GroupScheme.baseChange (algebraBaseMap k K)).obj G))
    (eT : p.torus ≅ ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T))
    (hT : p.inclusion = CommGroupScheme.groupHom eT.hom ≫
      (GroupScheme.baseChange (algebraBaseMap k K)).map i)

include hT in
/-- Coefficient conjugation carries the representative around `v` to the representative
around the conjugate point, when the roots correspond. -/
theorem rootPointReflectionRepresentative_rationalConjugate (σ : K ≃ₐ[k] K)
    {α β : p.rootIndex}
    (hroot : characterLattice.congr eT (p.rootDatum.root β) =
      characterLattice.galoisRepresentation k K T σ
        (characterLattice.congr eT (p.rootDatum.root α)))
    {v w : rationalPoints (baseChanged k K G)}
    (hv : v ∈ (RelativeRoot.subgroup p.inclusion (p.rootDatum.root α)).carrier
      (Over.mk (𝟙 _))) (hv1 : v ≠ 1)
    (hw : w ∈ (RelativeRoot.subgroup p.inclusion (p.rootDatum.root β)).carrier
      (Over.mk (𝟙 _))) (hw1 : w ≠ 1)
    (hvw : rationalConjugate k K G σ v = w) :
    rationalConjugate k K G σ (p.rootPointReflectionRepresentative hv hv1).point =
      (p.rootPointReflectionRepresentative hw hw1).point := by
  have hx := (p.rootPointOppositePair_spec hv hv1).changeTorus eT hT
  have hq := hx.rationalConjugate k K i σ
  rw [← hroot, hvw] at hq
  have he := p.eq_rootPointOppositePair hw hw1
    ((RelativeRoot.isOppositeFactorPair_changeTorus_iff eT hT).mp hq)
  rw [rootPointReflectionRepresentative_point, rootPointReflectionRepresentative_point,
    map_mul, map_mul, hvw, ← he]

end Galois

end SplitPinning

/-! ### Merged-root data of Galois-compatible pinnings -/

section Compatible

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance : IsAffineHom
    ((GroupScheme.baseChange (algebraBaseMap k K)).obj G).X.hom := by
  change IsAffineHom (pullback.snd G.X.hom (algebraBaseMap k K))
  infer_instance

namespace GaloisCompatiblePinningData

variable (D : GaloisCompatiblePinningData k K G)

/-- The root map of `b` conjugated by the canonical representative of `a`: a root map of
any index `r` whose root is `a + b`, when `⟨b, a^∨⟩ = -1`. -/
def mergedRootMap (a b : D.pinning.base.support) (r : D.pinning.rootIndex)
    (hba : D.pinning.rootDatum.pairing (b : D.pinning.rootIndex) (a : D.pinning.rootIndex) =
      -1)
    (hr : D.pinning.rootDatum.root r =
      D.pinning.rootDatum.root (a : D.pinning.rootIndex) +
        D.pinning.rootDatum.root (b : D.pinning.rootIndex)) :
    D.pinning.RootParametrization r :=
  (D.rootMaps b).toRootParametrization.conjugate
    (SplitPinning.canonicalSimpleReflectionRepresentatives D.rootMaps a).normalizerPoint (by
      rw [SplitPinning.SimpleReflectionRepresentative.weylAction_normalizerPoint,
        ← RootPairing.root_reflectionPerm,
        SplitPinning.root_reflectionPerm_of_pairing_eq_neg_one a b hba, hr])

theorem mergedRootMap_rationalPoint (a b : D.pinning.base.support) (r : D.pinning.rootIndex)
    (hba : D.pinning.rootDatum.pairing (b : D.pinning.rootIndex) (a : D.pinning.rootIndex) =
      -1)
    (hr : D.pinning.rootDatum.root r =
      D.pinning.rootDatum.root (a : D.pinning.rootIndex) +
        D.pinning.rootDatum.root (b : D.pinning.rootIndex)) (s : K) :
    (D.mergedRootMap a b r hba hr).rationalPoint s =
      (SplitPinning.canonicalSimpleReflectionRepresentatives D.rootMaps a).point *
        (D.rootMaps b).toRootParametrization.rationalPoint s *
          ((SplitPinning.canonicalSimpleReflectionRepresentatives D.rootMaps a).point)⁻¹ :=
  SplitPinning.RootParametrization.conjugate_rationalPoint _ _ _ s

/-- The conjugated root maps are transported exactly by coefficient conjugation. -/
theorem mergedRootMap_rationalConjugate (σ : K ≃ₐ[k] K) (a b : D.pinning.base.support)
    (r r' : D.pinning.rootIndex)
    (hba : D.pinning.rootDatum.pairing (b : D.pinning.rootIndex) (a : D.pinning.rootIndex) =
      -1)
    (hr : D.pinning.rootDatum.root r =
      D.pinning.rootDatum.root (a : D.pinning.rootIndex) +
        D.pinning.rootDatum.root (b : D.pinning.rootIndex))
    (hba' : D.pinning.rootDatum.pairing (D.action σ b : D.pinning.rootIndex)
      (D.action σ a : D.pinning.rootIndex) = -1)
    (hr' : D.pinning.rootDatum.root r' =
      D.pinning.rootDatum.root (D.action σ a : D.pinning.rootIndex) +
        D.pinning.rootDatum.root (D.action σ b : D.pinning.rootIndex)) (s : K) :
    GaloisPointComparison.rationalConjugate k K G σ
        ((D.mergedRootMap a b r hba hr).rationalPoint s) =
      (D.mergedRootMap (D.action σ a) (D.action σ b) r' hba' hr').rationalPoint (σ s) := by
  rw [mergedRootMap_rationalPoint, mergedRootMap_rationalPoint, map_mul, map_mul, map_inv,
    SplitPinning.RootMapsGaloisCompatible.rationalPoints k K G D.rootMaps D.action
      D.rootMaps_compatible σ b s,
    SplitPinning.canonicalSimpleReflectionRepresentatives_rationalConjugate
      k K D.inclusion D.pinning D.torusIso D.inclusion_eq D.rootMaps D.action D.action_root
      (SplitPinning.RootMapsGaloisCompatible.unitPoints k K
        D.pinning D.rootMaps D.action D.rootMaps_compatible) σ a]

/-- Up to a nonzero scalar, coefficient conjugation carries the merged root map of `(a, b)`
to the merged root map of any ordering of `(σ a, σ b)`. -/
theorem exists_mergedRootMap_rationalConjugate (σ : K ≃ₐ[k] K)
    (a b a' b' : D.pinning.base.support) (r r' : D.pinning.rootIndex)
    (hba : D.pinning.rootDatum.pairing (b : D.pinning.rootIndex) (a : D.pinning.rootIndex) =
      -1)
    (hr : D.pinning.rootDatum.root r =
      D.pinning.rootDatum.root (a : D.pinning.rootIndex) +
        D.pinning.rootDatum.root (b : D.pinning.rootIndex))
    (hab' : D.pinning.rootDatum.pairing (a' : D.pinning.rootIndex)
      (b' : D.pinning.rootIndex) = -1)
    (hba' : D.pinning.rootDatum.pairing (b' : D.pinning.rootIndex)
      (a' : D.pinning.rootIndex) = -1)
    (hr' : D.pinning.rootDatum.root r' =
      D.pinning.rootDatum.root (a' : D.pinning.rootIndex) +
        D.pinning.rootDatum.root (b' : D.pinning.rootIndex))
    (hor : (a' = D.action σ a ∧ b' = D.action σ b) ∨
      (a' = D.action σ b ∧ b' = D.action σ a)) :
    ∃ f : K, f ≠ 0 ∧ ∀ s : K,
      GaloisPointComparison.rationalConjugate k K G σ
          ((D.mergedRootMap a b r hba hr).rationalPoint s) =
        (D.mergedRootMap a' b' r' hba' hr').rationalPoint (σ s * f) := by
  rcases hor with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · refine ⟨1, one_ne_zero, fun s => ?_⟩
    rw [mul_one]
    exact D.mergedRootMap_rationalConjugate σ a b r r' hba hr hba' hr' s
  · have hr'' : D.pinning.rootDatum.root r' =
        D.pinning.rootDatum.root (D.action σ a : D.pinning.rootIndex) +
          D.pinning.rootDatum.root (D.action σ b : D.pinning.rootIndex) :=
      hr'.trans (add_comm _ _)
    let Z := D.mergedRootMap (D.action σ a) (D.action σ b) r' hab' hr''
    refine ⟨Z.comparisonScalar (D.mergedRootMap _ _ r' hba' hr'),
      Z.comparisonScalar_ne_zero _, fun s => ?_⟩
    rw [D.mergedRootMap_rationalConjugate σ a b r r' hba hr hab' hr'' s]
    exact Z.rationalPoint_eq_comparisonScalar _ (σ s)

/-- Coroots follow roots under the ordinary Galois action on the descended torus. -/
theorem coroot_galoisRepresentation (σ : K ≃ₐ[k] K) {α β : D.pinning.rootIndex}
    (hroot : characterLattice.congr D.torusIso (D.pinning.rootDatum.root β) =
      characterLattice.galoisRepresentation k K D.torus σ
        (characterLattice.congr D.torusIso (D.pinning.rootDatum.root α))) :
    cocharacterLattice.congr D.torusIso (D.pinning.rootDatum.coroot β) =
      cocharacterLattice.galoisRepresentation k K D.torus σ
        (cocharacterLattice.congr D.torusIso (D.pinning.rootDatum.coroot α)) := by
  let : Smooth ((GroupScheme.baseChange (algebraBaseMap k K)).obj G).X.hom :=
    D.pinning.isConnectedReductive.smooth
  have : IsClosedImmersion D.pinning.inclusion.hom.hom.left := D.pinning.isMaximalTorus.2.1
  let eG : ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj D.torus).toGrp ≅
      D.pinning.torus.toGrp :=
    { hom := CommGroupScheme.groupHom D.torusIso.inv
      inv := CommGroupScheme.groupHom D.torusIso.hom
      hom_inv_id := congrArg Additive.toMul D.torusIso.inv_hom_id
      inv_hom_id := congrArg Additive.toMul D.torusIso.hom_inv_id }
  have hTK : IsSplitTorus
      ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj D.torus).toGrp :=
    IsSplitTorus.of_iso eG D.pinning.isSplitTorus
  have hmap : (GroupScheme.baseChange (algebraBaseMap k K)).map D.inclusion =
      eG.hom ≫ D.pinning.inclusion := by
    rw [D.inclusion_eq, ← Category.assoc]
    change _ = CommGroupScheme.groupHom (D.torusIso.inv ≫ D.torusIso.hom) ≫ _
    rw [Iso.inv_hom_id]
    exact (Category.id_comp _).symm
  have : IsIso eG.hom.hom.hom.left :=
    ⟨⟨eG.inv.hom.hom.left, congrArg (fun f => f.hom.hom.left) eG.hom_inv_id,
      congrArg (fun f => f.hom.hom.left) eG.inv_hom_id⟩⟩
  have hi : IsClosedImmersion
      ((GroupScheme.baseChange (algebraBaseMap k K)).map D.inclusion).hom.hom.left := by
    rw [hmap, Grp.comp_hom_hom, Over.comp_left]
    infer_instance
  have : Finite (weylImage (T := (CommGroupScheme.baseChange (algebraBaseMap k K)).obj D.torus)
      ((GroupScheme.baseChange (algebraBaseMap k K)).map D.inclusion)) :=
    splitTorusWeylImageFinite K _ _ hTK _ hi
  have hP : IsRootDatumOf (T := (CommGroupScheme.baseChange (algebraBaseMap k K)).obj D.torus)
      ((GroupScheme.baseChange (algebraBaseMap k K)).map D.inclusion)
      (torusTransportRootDatum D.torusIso D.pinning.rootDatum) :=
    IsRootDatumOf.torusTransport D.torusIso (Iso.refl _)
      (by rw [Iso.refl_hom, Category.comp_id]; exact D.inclusion_eq) D.pinning.isRootDatum
  have hidx : IsRootDatumOf.galoisRootIndexEquiv k K D.inclusion hP σ α = β := by
    apply (torusTransportRootDatum D.torusIso D.pinning.rootDatum).root.injective
    rw [IsRootDatumOf.galoisRootIndexEquiv_root, torusTransportRootDatum_root,
      torusTransportRootDatum_root, hroot]
  have h := IsRootDatumOf.galoisRootIndexEquiv_coroot k K D.inclusion hP σ α
  rw [hidx, torusTransportRootDatum_coroot, torusTransportRootDatum_coroot] at h
  exact h

section Family

variable {J : Type v} [MulAction (K ≃ₐ[k] K) J] (a b : J → D.pinning.base.support)

/-- The merged index `s_a(b)` of each pair. -/
def mergedIndex (c : J) : D.pinning.rootIndex :=
  D.pinning.rootDatum.reflectionPerm (a c : D.pinning.rootIndex) (b c : D.pinning.rootIndex)

variable (hba : ∀ c, D.pinning.rootDatum.pairing (b c : D.pinning.rootIndex)
  (a c : D.pinning.rootIndex) = -1)

omit [MulAction (K ≃ₐ[k] K) J] in
include hba in
theorem root_mergedIndex (c : J) :
    D.pinning.rootDatum.root (D.mergedIndex a b c) =
      D.pinning.rootDatum.root (a c : D.pinning.rootIndex) +
        D.pinning.rootDatum.root (b c : D.pinning.rootIndex) :=
  SplitPinning.root_reflectionPerm_of_pairing_eq_neg_one (a c) (b c) (hba c)

/-- The merged root map of each pair, before normalization. -/
def mergedFamilyMap (c : J) : D.pinning.RootParametrization (D.mergedIndex a b c) :=
  D.mergedRootMap (a c) (b c) (D.mergedIndex a b c) (hba c) (D.root_mergedIndex a b hba c)

variable {a b}

/-- The merged roots are permuted by the ordinary Galois action when each pair is carried to
its image pair in either order. -/
theorem root_mergedIndex_galois (hba : ∀ c, D.pinning.rootDatum.pairing
      (b c : D.pinning.rootIndex) (a c : D.pinning.rootIndex) = -1)
    (horient : ∀ (σ : K ≃ₐ[k] K) (c : J),
      (a (σ • c) = D.action σ (a c) ∧ b (σ • c) = D.action σ (b c)) ∨
        (a (σ • c) = D.action σ (b c) ∧ b (σ • c) = D.action σ (a c)))
    (σ : K ≃ₐ[k] K) (c : J) :
    characterLattice.congr D.torusIso (D.pinning.rootDatum.root (D.mergedIndex a b (σ • c))) =
      characterLattice.galoisRepresentation k K D.torus σ
        (characterLattice.congr D.torusIso (D.pinning.rootDatum.root (D.mergedIndex a b c))) := by
  rw [D.root_mergedIndex a b hba, D.root_mergedIndex a b hba, map_add, map_add, map_add]
  rcases horient σ c with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2, D.action_root, D.action_root]
  · rw [h1, h2, D.action_root, D.action_root, add_comm]

end Family

/-- **Galois-compatible merged-root data.** Let `J` carry an action of the automorphism
group and let `a, b : J → Δ` be distinct simple roots with mutual pairings `-1`, carried by
each `σ` to the pair at `σ c` in one of the two orders. Then there is merged-root data
`M c` with `a`, `b` as given and `c_a = c_b = 1`, whose representative is generated by the
rational root subgroups of `± α`, and whose root map, representative and coroot are carried
exactly to those at `σ c` by coefficient conjugation. -/
theorem exists_mergedRootGaloisData [FiniteDimensional k K]
    {J : Type v} [MulAction (K ≃ₐ[k] K) J] (a b : J → D.pinning.base.support)
    (hab : ∀ c, a c ≠ b c ∧
      D.pinning.rootDatum.pairing (a c : D.pinning.rootIndex) (b c : D.pinning.rootIndex) =
        -1 ∧
      D.pinning.rootDatum.pairing (b c : D.pinning.rootIndex) (a c : D.pinning.rootIndex) =
        -1)
    (horient : ∀ (σ : K ≃ₐ[k] K) (c : J),
      (a (σ • c) = D.action σ (a c) ∧ b (σ • c) = D.action σ (b c)) ∨
        (a (σ • c) = D.action σ (b c) ∧ b (σ • c) = D.action σ (a c))) :
    ∃ M : J → D.pinning.SteinbergModifiedData,
      (∀ c, (M c).a = a c ∧ (M c).b = b c ∧ (M c).ca = 1 ∧ (M c).cb = 1) ∧
      (∀ c, (M c).nAlpha.point ∈
        (RelativeRoot.subgroup D.pinning.inclusion
            (D.pinning.rootDatum.root (M c).alpha)).carrier (Over.mk (𝟙 _)) ⊔
          (RelativeRoot.subgroup D.pinning.inclusion
            (-D.pinning.rootDatum.root (M c).alpha)).carrier (Over.mk (𝟙 _))) ∧
      (∀ (σ : K ≃ₐ[k] K) (c : J) (s : K),
        GaloisPointComparison.rationalConjugate k K G σ ((M c).xAlpha.rationalPoint s) =
          (M (σ • c)).xAlpha.rationalPoint (σ s)) ∧
      (∀ (σ : K ≃ₐ[k] K) (c : J),
        GaloisPointComparison.rationalConjugate k K G σ (M c).nAlpha.point =
          (M (σ • c)).nAlpha.point) ∧
      (∀ (σ : K ≃ₐ[k] K) (c : J) (t : Kˣ),
        GaloisPointComparison.rationalConjugate k K G σ
            (SplitPinning.corootRationalPoint D.pinning (M c).alpha t) =
          SplitPinning.corootRationalPoint D.pinning (M (σ • c)).alpha
            (Units.map σ.toMonoidHom t)) := by
  have hba : ∀ c, D.pinning.rootDatum.pairing (b c : D.pinning.rootIndex)
      (a c : D.pinning.rootIndex) = -1 := fun c => (hab c).2.2
  -- semilinearity of the unnormalized merged root maps
  have hsemi : ∀ (σ : K ≃ₐ[k] K) (c : J), ∃ f : K, f ≠ 0 ∧ ∀ s : K,
      GaloisPointComparison.rationalConjugate k K G σ
          ((D.mergedFamilyMap a b hba c).rationalPoint s) =
        (D.mergedFamilyMap a b hba (σ • c)).rationalPoint (σ s * f) := fun σ c =>
    D.exists_mergedRootMap_rationalConjugate σ (a c) (b c) (a (σ • c)) (b (σ • c))
      (D.mergedIndex a b c) (D.mergedIndex a b (σ • c)) (hba c)
      (D.root_mergedIndex a b hba c) (hab (σ • c)).2.1 (hba (σ • c))
      (D.root_mergedIndex a b hba (σ • c)) (horient σ c)
  choose φ hφ0 hφ using hsemi
  -- the scalars form a twisted cocycle
  have hcoc : ∀ (σ τ : K ≃ₐ[k] K) (c : J), φ (σ * τ) c = σ (φ τ c) * φ σ (τ • c) := by
    intro σ τ c
    have h1 := hφ (σ * τ) c 1
    rw [GaloisPointComparison.rationalConjugate_mul, hφ τ c 1, hφ σ (τ • c), map_one,
      map_one, one_mul, one_mul, mul_smul] at h1
    exact ((D.mergedFamilyMap a b hba (σ • τ • c)).rationalPoint_injective h1).symm
  obtain ⟨mu, hmu0, hmu⟩ := exists_galoisTwist φ hφ0 hcoc
  -- normalized merged root maps
  let xα : (c : J) → D.pinning.RootParametrization (D.mergedIndex a b c) := fun c =>
    (D.mergedFamilyMap a b hba c).scale (Units.mk0 (mu c) (hmu0 c))
  have hx : ∀ (σ : K ≃ₐ[k] K) (c : J) (s : K),
      GaloisPointComparison.rationalConjugate k K G σ ((xα c).rationalPoint s) =
        (xα (σ • c)).rationalPoint (σ s) := by
    intro σ c s
    simp only [xα, SplitPinning.RootParametrization.scale_rationalPoint, Units.val_mk0]
    rw [hφ, hmu, map_mul]
    congr 1
    ring
  -- the Galois-compatible nonidentity points and their representatives
  have hv : ∀ c, (xα c).rationalPoint 1 ∈
      (RelativeRoot.subgroup D.pinning.inclusion
        (D.pinning.rootDatum.root (D.mergedIndex a b c))).carrier (Over.mk (𝟙 _)) :=
    fun c => (xα c).rationalPoint_mem 1
  have hv1 : ∀ c, (xα c).rationalPoint 1 ≠ 1 :=
    fun c => (xα c).rationalPoint_ne_one one_ne_zero
  let nα : (c : J) → D.pinning.ReflectionRepresentative (D.mergedIndex a b c) := fun c =>
    D.pinning.rootPointReflectionRepresentative (hv c) (hv1 c)
  have hn : ∀ (σ : K ≃ₐ[k] K) (c : J),
      GaloisPointComparison.rationalConjugate k K G σ (nα c).point = (nα (σ • c)).point :=
    fun σ c =>
      SplitPinning.rootPointReflectionRepresentative_rationalConjugate k K D.inclusion
        D.pinning D.torusIso D.inclusion_eq σ (D.root_mergedIndex_galois hba horient σ c)
        (hv c) (hv1 c) (hv (σ • c)) (hv1 (σ • c)) (by simpa only [map_one] using hx σ c 1)
  refine ⟨fun c =>
    { a := a c
      b := b c
      a_ne_b := (hab c).1
      alpha := D.mergedIndex a b c
      root_eq := D.root_mergedIndex a b hba c
      xAlpha := xα c
      nAlpha := nα c
      ca := 1
      cb := 1
      ca_ne_zero := one_ne_zero
      cb_ne_zero := one_ne_zero },
    fun c => ⟨rfl, rfl, rfl, rfl⟩,
    fun c => D.pinning.rootPointReflectionRepresentative_mem_generated (hv c) (hv1 c),
    hx, hn, fun σ c t => ?_⟩
  exact SplitPinning.corootRationalPoint_rationalConjugate k K D.torus D.inclusion D.pinning
    D.torusIso D.inclusion_eq σ _ _
    (D.coroot_galoisRepresentation σ (D.root_mergedIndex_galois hba horient σ c)) t

end GaloisCompatiblePinningData

end Compatible

end Langlands.GroupScheme
