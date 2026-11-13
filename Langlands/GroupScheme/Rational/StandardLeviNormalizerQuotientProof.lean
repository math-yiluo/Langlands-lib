import Langlands.GroupScheme.Rational.StandardLeviWeylStatements
import Langlands.GroupScheme.Rational.PointContainmentFromDensity
import Langlands.GroupScheme.Rational.StandardRepresentability
import Langlands.GroupScheme.Rational.MaximalSplitTorusSubgroup
import Langlands.GroupScheme.Rational.MaximalSplitTorusConjugacyProof
import Langlands.GroupScheme.Rational.StandardCocharacterProof
import Langlands.GroupScheme.Dynamic.CentralizerReductiveProof
import Langlands.GroupScheme.ConjugacyBaseChange
import Langlands.GroupScheme.HomConjugacy
import Langlands.GroupScheme.Torus.SplitReductiveProof
import Langlands.GroupScheme.Rational.StandardLeviSplitComponentProof

/-! # Proof of Renard V.4.3.3: `W(M, M)/W_M ≃ N_G(M)/M` for standard Levi subgroups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

open Langlands.Aubert.General.RationalPointFamily
open Langlands.AlgebraicGeometry.PointTopology

namespace StandardLeviNormalizerQuotient

section Conj

variable {Γ : Type*} [Group Γ] {H : Subgroup Γ} {g : Γ}

/-- An element whose conjugation preserves `H` conjugates elements of `H` into `H`. -/
theorem conj_mem_of_map_eq (h : H.map (MulAut.conj g : Γ →* Γ) = H) {z : Γ} (hz : z ∈ H) :
    g * z * g⁻¹ ∈ H :=
  h ▸ ⟨z, hz, rfl⟩

/-- An element whose conjugation preserves `H` has inverse-conjugation preserving `H`. -/
theorem inv_conj_mem_of_map_eq (h : H.map (MulAut.conj g : Γ →* Γ) = H) {z : Γ} (hz : z ∈ H) :
    g⁻¹ * z * g ∈ H := by
  rw [← h] at hz
  obtain ⟨w, hw, rfl⟩ := hz
  simpa [mul_assoc] using hw

/-- If conjugation by `g` preserves `H` and `m ∈ H`, conjugation by `m * g` preserves `H`. -/
theorem map_conj_mul_eq (h : H.map (MulAut.conj g : Γ →* Γ) = H) {m : Γ} (hm : m ∈ H) :
    H.map (MulAut.conj (m * g) : Γ →* Γ) = H := by
  apply le_antisymm
  · rintro x ⟨y, hy, rfl⟩
    have h1 := H.mul_mem (H.mul_mem hm (conj_mem_of_map_eq h hy)) (H.inv_mem hm)
    simpa [mul_assoc] using h1
  · intro x hx
    have h1 : m⁻¹ * x * m ∈ H := H.mul_mem (H.mul_mem (H.inv_mem hm) hx) hm
    refine ⟨g⁻¹ * (m⁻¹ * x * m) * g, inv_conj_mem_of_map_eq h h1, ?_⟩
    simp [mul_assoc]

end Conj

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)

/-- Clause 1 of V.4.3.3: a normalizer point has class in `W_I` exactly when it lies in
`L_I(k)`. -/
theorem mk_mem_standardRelativeWeylGroup_iff (I : Finset (SimpleRoot i ν))
    (n : normalizerPoints i) :
    (QuotientGroup.mk n : relativeWeylGroup i) ∈
        standardRelativeWeylGroup i ν (rootSet i ν I) ↔
      (n : RationalPoint k G.X) ∈ levi i ν I := by
  constructor
  · rintro ⟨n', hn', he⟩
    have hc' : n'⁻¹ * n ∈ (centralizerPoints i).subgroupOf (normalizerPoints i) :=
      QuotientGroup.eq.mp he
    have hc : ((n'⁻¹ * n : normalizerPoints i) : RationalPoint k G.X) ∈ centralizerPoints i :=
      Subgroup.mem_subgroupOf.mp hc'
    have h := (levi i ν I).mul_mem (show (n' : RationalPoint k G.X) ∈ levi i ν I from hn')
      (centralizerPoints_le_levi i ν I hc)
    simpa using h
  · intro hn
    exact ⟨n, hn, rfl⟩

omit [IsAffineHom G.X.hom] in
/-- The point of `G` through which an inner automorphism acts on base points. -/
theorem comp_innerIso_hom_base (g x : RationalPoint k G.X) :
    x ≫ (G.innerIso g).hom.hom.hom = g * x * g⁻¹ := by
  rw [comp_innerIso_hom, constantPoint_self]

variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/-- Clause 2 of V.4.3.3: every `g ∈ G(k)` normalizing `L_I(k)` lies in `n L_I(k)` for a
normalizer point `n` normalizing `L_I(k)`. -/
theorem exists_normalizerPoint_of_map_conj_eq (hG : IsConnectedReductive G)
    (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν)
    (I : Finset (SimpleRoot i ν)) (g : RationalPoint k G.X)
    (hg : (levi i ν I).map
        (MulAut.conj g : RationalPoint k G.X →* RationalPoint k G.X) = levi i ν I) :
    ∃ n : normalizerPoints i,
      (levi i ν I).map (MulAut.conj (n : RationalPoint k G.X) :
          RationalPoint k G.X →* RationalPoint k G.X) = levi i ν I ∧
        (n : RationalPoint k G.X)⁻¹ * g ∈ levi i ν I := by
  set J := rootSet i ν I with hJdef
  have hJ : J ⊆ simpleRelativeRoots i ν := rootSet_subset i ν I
  have hS : IsSplitTorus T.toGrp := hi.isSplitSubtorus.1
  have : Smooth T.toGrp.X.hom := hS.smooth
  have : IsAffineHom T.toGrp.X.hom := hS.isAffineHom
  have : ConnectedSpace T.toGrp.X.left := hS.connectedSpace
  have hrep := Standard.isRepresentedBy_leviHom i ν J
  have hclosed := Standard.isClosedSubgroup_leviHom i ν J
  -- The conjugate torus `g i g⁻¹`.
  let i' : T.toGrp ⟶ G := i ≫ (G.innerIso g).hom
  have hpts : (SubgroupFunctor.range i').carrier (Over.mk (𝟙 _)) ≤
      (SubgroupFunctor.range (Standard.leviHom i ν J)).carrier (Over.mk (𝟙 _)) := by
    rw [hrep.2]
    intro x hx
    obtain ⟨t, rfl⟩ := SubgroupFunctor.mem_range.mp hx
    have ht : t ≫ i.hom.hom ∈ levi i ν I := torusPoints_le_levi i ν I ⟨t, rfl⟩
    have hconj := conj_mem_of_map_eq hg ht
    have he : t ≫ i'.hom.hom = g * (t ≫ i.hom.hom) * g⁻¹ := by
      rw [← comp_innerIso_hom_base g (t ≫ i.hom.hom)]
      simp only [i', Grp.comp_hom_hom, Category.assoc]
    rw [he]
    exact hconj
  have hrange' : SubgroupFunctor.range i' ≤ standardLevi i ν J :=
    hrep.2 ▸ SubgroupFunctor.range_le_of_localField_points hclosed hpts
  have hrange : SubgroupFunctor.range i ≤ standardLevi i ν J :=
    (range_le_torusCentralizer i).trans (torusCentralizer_le_standardLevi i ν J)
  -- Both tori are maximal split in the standard Levi.
  have hi' : IsMaximalSplitTorus i' := hi.comp_iso (G.innerIso g)
  let f := hrep.factorHom i' hrange'
  let f₀ := hrep.factorHom i hrange
  have hf : f ≫ Standard.leviHom i ν J = i' := hrep.factorHom_comp i' hrange'
  have hf₀ : f₀ ≫ Standard.leviHom i ν J = i := hrep.factorHom_comp i hrange
  have hfmax : IsMaximalSplitTorus f := hi'.isMaximalSplitTorus_factorHom hrep hclosed hrange'
  have hf₀max : IsMaximalSplitTorus f₀ := hi.isMaximalSplitTorus_factorHom hrep hclosed hrange
  have hM := (standardLeviSplitComponentStatement k G hG T i hi ν hν J hJ).1
  obtain ⟨m, e, hme⟩ := (maximalSplitTorusConjugacy k _ hM).1 T T f f₀ hfmax hf₀max
  -- Transport the conjugacy to `G`.
  set m' : RationalPoint k G.X := m ≫ (Standard.leviHom i ν J).hom.hom with hm'def
  have hm' : m' ∈ levi i ν I := by
    show m' ∈ (standardLevi i ν J).carrier _
    rw [← hrep.2]
    exact ⟨m, rfl⟩
  have hconj : i ≫ (G.innerIso (m' * g)).hom = e.hom ≫ i := by
    have h1 := congrArg (· ≫ Standard.leviHom i ν J) hme
    simp only [Category.assoc] at h1
    rw [innerIso_hom_comp, ← Category.assoc, hf, hf₀] at h1
    rw [innerIso_mul_hom, ← Category.assoc]
    exact h1
  let e' : T ≅ T :=
    { hom := Additive.ofMul e.hom
      inv := Additive.ofMul e.inv
      hom_inv_id := congrArg Additive.ofMul e.hom_inv_id
      inv_hom_id := congrArg Additive.ofMul e.inv_hom_id }
  have hn : m' * g ∈ normalizerPoints i := ⟨e', hconj⟩
  refine ⟨⟨m' * g, hn⟩, map_conj_mul_eq hg hm', ?_⟩
  have h := inv_conj_mem_of_map_eq hg ((levi i ν I).inv_mem hm')
  simpa [mul_assoc] using h

end StandardLeviNormalizerQuotient

open StandardLeviNormalizerQuotient in
/-- **Renard V.4.3.3.** For a standard Levi subgroup `M = L_I` of a connected reductive
group over a nonarchimedean local field, a normalizer point has class in `W_M` exactly when
it lies in `M(k)`, and every element of `G(k)` normalizing `M(k)` lies in `n M(k)` for a
normalizer point `n` normalizing `M(k)`: `W(M, M)/W_M ≃ N_{G(k)}(M(k))/M(k)`. -/
theorem standardLeviNormalizerQuotient : StandardLeviNormalizerQuotientStatement.{u} := by
  intro k _ _ _ _ G hG T i hi ν
  have := hG.isAffineHom
  have := hi.isSplitSubtorus.mono
  intro hν I
  exact ⟨fun n => mk_mem_standardRelativeWeylGroup_iff i ν I n,
    fun g hg => exists_normalizerPoint_of_map_conj_eq i ν hG hi hν I g hg⟩

end Langlands.GroupScheme
