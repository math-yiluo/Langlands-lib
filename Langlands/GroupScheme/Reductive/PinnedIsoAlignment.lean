import Langlands.GroupScheme.Reductive.StarActionIndependenceProof

/-! # Aligning a geometric isomorphism with two based root data -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SplitPinning

variable {k : Type u} [Field k]
  {G H : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
  (p : SplitPinning G) (q : SplitPinning H)

/-- Any actual isomorphism between groups with split pinnings carries the chosen
maximal tori to each other after a rational inner postcomposition. -/
theorem exists_inner_comp_torusCompatible (E : G ≅ H) :
    ∃ (g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ H.X) (φ : p.torus ≅ q.torus),
      p.inclusion ≫ (E ≪≫ H.innerIso g).hom =
        CommGroupScheme.groupHom φ.hom ≫ q.inclusion := by
  have hH := q.isConnectedReductive
  let := hH.smooth
  let := hH.connectedSpace
  obtain ⟨g, t, h⟩ := smoothMaximalSplitTorusConjugacy k H p.torus q.torus
    (p.inclusion ≫ E.hom) q.inclusion
    ((p.isMaximalTorus.comp_iso E).isMaximalSplitTorus p.isSplitTorus)
    (q.isMaximalTorus.isMaximalSplitTorus q.isSplitTorus)
  refine ⟨g, CommGroupScheme.isoOfGroupIso t, ?_⟩
  rw [Iso.trans_hom, ← Category.assoc]
  exact h

/-- A rational normalizer correction makes a torus-compatible isomorphism preserve
the bases of the supplied root data. -/
theorem exists_inner_comp_based_of_torusCompatible
    (E : G ≅ H) (φ : p.torus ≅ q.torus)
    (ht : p.inclusion ≫ E.hom = CommGroupScheme.groupHom φ.hom ≫ q.inclusion) :
    ∃ (g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ H.X)
      (ψ : p.torus ≅ q.torus) (e : RootPairing.Equiv p.rootDatum q.rootDatum),
      p.inclusion ≫ (E ≪≫ H.innerIso g).hom =
        CommGroupScheme.groupHom ψ.hom ≫ q.inclusion ∧
      (∀ χ, e.weightMap χ = ψ.inv ≫ χ) ∧
      (∀ a, a ∈ p.base.support ↔ e.indexEquiv a ∈ q.base.support) := by
  have hsq : q.inclusion ≫ E.inv =
      CommGroupScheme.groupHom φ.inv ≫ p.inclusion := by
    rw [Iso.comp_inv_eq, Category.assoc, ht, ← Category.assoc]
    change q.inclusion = CommGroupScheme.groupHom (φ.inv ≫ φ.hom) ≫ q.inclusion
    rw [Iso.inv_hom_id]
    exact (Category.id_comp q.inclusion).symm
  let e₀ : RootPairing.Equiv p.rootDatum q.rootDatum :=
    rootDatumEquivOfTorusCompatibleIso q.isConnectedReductive p.isConnectedReductive
      q.isSplitTorus p.isSplitTorus q.isMaximalTorus p.isMaximalTorus
      E.symm φ.symm hsq q.isRootDatum p.isRootDatum
  have he₀ (χ : characterLattice p.torus) : e₀.weightMap χ = φ.inv ≫ χ :=
    rootDatumEquivOfTorusCompatibleIso_weightMap q.isConnectedReductive
      p.isConnectedReductive q.isSplitTorus p.isSplitTorus q.isMaximalTorus
      p.isMaximalTorus E.symm φ.symm hsq
      q.isRootDatum p.isRootDatum χ
  obtain ⟨w, hw, hbase⟩ := StarActionIndependence.exists_weyl_comp_preserves_base p q e₀
  let : IsClosedImmersion q.inclusion.hom.hom.left := q.isMaximalTorus.2.1
  have hW := (weylGroup k H q.isConnectedReductive q.torus q.isSplitTorus q.inclusion
    q.isMaximalTorus q.rootIndex q.rootDatum q.isRootDatum).1
  have hwi : RootPairing.Equiv.weightHom q.rootDatum w ∈ weylImage q.inclusion := by
    rw [hW]
    exact Subgroup.mem_map_of_mem _ hw
  obtain ⟨n, hn⟩ := MonoidHom.mem_range.1 hwi
  have hτ := isNormalizingPoint_normalizingAut q.inclusion n
  refine ⟨n.val, φ ≪≫ normalizingAut q.inclusion n,
    RootPairing.Equiv.comp w e₀, ?_, fun χ => ?_, hbase⟩
  · rw [Iso.trans_hom, ← Category.assoc, ht, Category.assoc, hτ,
      ← Category.assoc]
    rfl
  · have h := DFunLike.congr_fun hn (e₀.weightMap χ)
    change (normalizingAut q.inclusion n).inv ≫ e₀.weightMap χ =
      w.weightMap (e₀.weightMap χ) at h
    change w.weightMap (e₀.weightMap χ) =
      ((normalizingAut q.inclusion n).inv ≫ φ.inv) ≫ χ
    rw [← h, he₀, Category.assoc]

/-- After an inner postcomposition, any actual isomorphism carries the chosen split
maximal tori to each other and induces an equivalence preserving the chosen bases. -/
theorem exists_inner_comp_based (E : G ≅ H) :
    ∃ (g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ H.X)
      (φ : p.torus ≅ q.torus) (e : RootPairing.Equiv p.rootDatum q.rootDatum),
      p.inclusion ≫ (E ≪≫ H.innerIso g).hom =
        CommGroupScheme.groupHom φ.hom ≫ q.inclusion ∧
      (∀ χ, e.weightMap χ = φ.inv ≫ χ) ∧
      (∀ a, a ∈ p.base.support ↔ e.indexEquiv a ∈ q.base.support) := by
  obtain ⟨g, φ, ht⟩ := p.exists_inner_comp_torusCompatible q E
  obtain ⟨n, ψ, e, hs, he, hb⟩ := p.exists_inner_comp_based_of_torusCompatible q
    (E ≪≫ H.innerIso g) φ ht
  refine ⟨n * g, ψ, e, ?_, he, hb⟩
  simpa only [Iso.trans_hom, innerIso_mul_hom, Category.assoc] using hs

/-- Existence of an inner adjustment carrying both chosen tori and bases to each other. -/
def InnerAlignmentStatement : Prop :=
  ∀ E : G ≅ H,
    ∃ (g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ H.X)
      (φ : p.torus ≅ q.torus) (e : RootPairing.Equiv p.rootDatum q.rootDatum),
      p.inclusion ≫ (E ≪≫ H.innerIso g).hom =
        CommGroupScheme.groupHom φ.hom ≫ q.inclusion ∧
      (∀ χ, e.weightMap χ = φ.inv ≫ χ) ∧
      (∀ a, a ∈ p.base.support ↔ e.indexEquiv a ∈ q.base.support)

/-- Inner alignment follows from rational torus conjugacy and the Weyl correction. -/
theorem innerAlignment : p.InnerAlignmentStatement q :=
  fun E => p.exists_inner_comp_based q E

end Langlands.GroupScheme.SplitPinning
