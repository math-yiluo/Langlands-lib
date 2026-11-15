import Langlands.GroupScheme.AlgebraicFundamentalGroupCentralTorusLattice
import Langlands.GroupScheme.AlgebraicFundamentalGroupCentralTorusGeometry
import Langlands.GroupScheme.AlgebraicFundamentalGroupMapProof
import Langlands.GroupScheme.AlgebraicFundamentalGroupCentralTorusStatement

/-! # Central-torus exactness of algebraic fundamental groups -/

noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.AlgebraicFundamentalGroup

/-- **Central-torus exactness of algebraic fundamental groups** (Kaletha–Prasad,
§11.5 and the proof of Lemma 11.5.1). If `Z` is a closed central torus of the connected
reductive group `H` and `p : H → G` is the fppf quotient by `Z`, then
`0 → π₁(Z) → π₁(H) → π₁(G) → 0` is exact for the selected induced maps. -/
theorem centralTorusFundamentalExactness :
    CentralTorusFundamentalExactnessStatement.{u} := by
  intro k E _ _ _ _ Z hZt H G hH hG i p hi hc hq
  have hZ : IsConnectedReductive Z.toGrp := hZt.isConnectedReductive_of_fieldSplitting
  obtain ⟨b, e, he⟩ := (chosenChoice k Z.toGrp hZ).exists_torusFactorization
    (chosenChoice k H hH) i
  obtain ⟨c, e', he'⟩ := b.exists_torusFactorization (chosenChoice k G hG) p
  have hZiso : IsIso (chosenChoice k Z.toGrp hZ).inclusion :=
    (chosenChoice k Z.toGrp hZ).isMaximal.isIso_of_torus hZt
  -- Geometric torus factorizations after base change to `E`.
  have hfac₁ : (chosenChoice k Z.toGrp hZ).IsTorusFactorization E b i
      ((CommGroupScheme.baseChange (algebraBaseMap k E)).map e) := by
    change (GroupScheme.baseChange (algebraBaseMap k E)).map
        (chosenChoice k Z.toGrp hZ).inclusion ≫
        (GroupScheme.baseChange (algebraBaseMap k E)).map i =
      (GroupScheme.baseChange (algebraBaseMap k E)).map (CommGroupScheme.groupHom e) ≫
        (GroupScheme.baseChange (algebraBaseMap k E)).map b.inclusion
    rw [← Functor.map_comp, ← Functor.map_comp, he]
  have hfac₂ : b.IsTorusFactorization E c p
      ((CommGroupScheme.baseChange (algebraBaseMap k E)).map e') := by
    change (GroupScheme.baseChange (algebraBaseMap k E)).map b.inclusion ≫
        (GroupScheme.baseChange (algebraBaseMap k E)).map p =
      (GroupScheme.baseChange (algebraBaseMap k E)).map (CommGroupScheme.groupHom e') ≫
        (GroupScheme.baseChange (algebraBaseMap k E)).map c.inclusion
    rw [← Functor.map_comp, ← Functor.map_comp, he']
  -- The induced maps at the factorizing choices, on representatives.
  have hmapZ := algebraicFundamentalGroupMap k E Z.toGrp H hZ hH
    (chosenChoice k Z.toGrp hZ) b i
  have hmapH := algebraicFundamentalGroupMap k E H G hH hG b c p
  have hcompZ := algebraicFundamentalGroupComparison k E Z.toGrp hZ
  have hcompH := algebraicFundamentalGroupComparison k E H hH
  have hcompG := algebraicFundamentalGroupComparison k E G hG
  have hm₁ : ∀ ν, (chosenChoice k Z.toGrp hZ).mapTo E b i
      (((chosenChoice k Z.toGrp hZ).corootImage E).mkQ ν) =
      (b.corootImage E).mkQ ((chosenChoice k Z.toGrp hZ).torusLatticeMap b E
        ((CommGroupScheme.baseChange (algebraBaseMap k E)).map e) ν) := by
    intro ν
    rw [hmapZ.2.1.2 b _ hfac₁ ν, hcompH.2.1 b]
    rfl
  have hm₂ : ∀ ν, b.mapTo E c p ((b.corootImage E).mkQ ν) =
      (c.corootImage E).mkQ (b.torusLatticeMap c E
        ((CommGroupScheme.baseChange (algebraBaseMap k E)).map e') ν) := by
    intro ν
    rw [hmapH.2.1.2 c _ hfac₂ ν, hcompG.2.1 c]
    rfl
  -- The preimage tori of the derived covers are identified compatibly with `p`.
  obtain ⟨ψ, hψ⟩ := CentralTorus.exists_coverIso (b := b) (c := c) hH hG hq hc
  obtain ⟨φ, hφ⟩ := CentralTorus.exists_scTorusIso ψ hψ he'
  let σ : b.scLattice E →ₗ[ℤ] c.scLattice E :=
    (cocharacterLattice.congr
      ((CommGroupScheme.baseChange (algebraBaseMap k E)).mapIso φ)).toAddMonoidHom.toIntLinearMap
  have hσ : Function.Bijective σ :=
    (cocharacterLattice.congr
      ((CommGroupScheme.baseChange (algebraBaseMap k E)).mapIso φ)).bijective
  have hσρ : ∀ s, c.corootMap E (σ s) = b.torusLatticeMap c E
      ((CommGroupScheme.baseChange (algebraBaseMap k E)).map e') (b.corootMap E s) := by
    intro s
    change (s ≫ (CommGroupScheme.baseChange (algebraBaseMap k E)).map φ.hom) ≫
        (CommGroupScheme.baseChange (algebraBaseMap k E)).map c.scToTorus =
      (s ≫ (CommGroupScheme.baseChange (algebraBaseMap k E)).map b.scToTorus) ≫
        (CommGroupScheme.baseChange (algebraBaseMap k E)).map e'
    rw [Category.assoc, Category.assoc, ← Functor.map_comp, ← Functor.map_comp, hφ]
  -- Exactness at the factorizing choices.
  have hexact := CentralTorus.torusLatticeMap_exact E hq hi hZiso he he'
  have hsurj := CentralTorus.torusLatticeMap_surjective E hH hG hZt hq hi hc he'
  have hm := quotient_exact_of_lattice_exact _ _ _ _ _ (b.corootMap E) (c.corootMap E) σ
    rfl rfl hexact.1 hexact.2 hsurj hσ hσρ (c.corootMap_injective E)
    ((chosenChoice k Z.toGrp hZ).mapTo E b i) (b.mapTo E c p) hm₁ hm₂
  -- Transport to the chosen presentations.
  have h₁ : ((chosenChoice k H hH).comparison E b).comp
      ((chosenChoice k Z.toGrp hZ).mapTo E (chosenChoice k H hH) i) =
      (chosenChoice k Z.toGrp hZ).mapTo E b i := by
    rw [(algebraicFundamentalGroupMap k E Z.toGrp H hZ hH (chosenChoice k Z.toGrp hZ)
      (chosenChoice k H hH) i).2.2.2 (chosenChoice k Z.toGrp hZ) b,
      hcompZ.2.1 (chosenChoice k Z.toGrp hZ), LinearMap.comp_id]
  have h₂' : ((chosenChoice k G hG).comparison E c).comp
      ((chosenChoice k H hH).mapTo E (chosenChoice k G hG) p) =
      (b.mapTo E c p).comp ((chosenChoice k H hH).comparison E b) :=
    (algebraicFundamentalGroupMap k E H G hH hG (chosenChoice k H hH)
      (chosenChoice k G hG) p).2.2.2 b c
  exact exact_of_comparison
    (fundamentalGroupMap k E Z.toGrp H hZ hH i) (fundamentalGroupMap k E H G hH hG p)
    ((chosenChoice k Z.toGrp hZ).mapTo E b i) (b.mapTo E c p)
    ((chosenChoice k H hH).comparison E b) ((chosenChoice k G hG).comparison E c)
    ((hcompH.1 (chosenChoice k H hH) b).2.2.1)
    ((hcompG.1 (chosenChoice k G hG) c).2.2.1.1) h₁ h₂' hm

end Langlands.GroupScheme.AlgebraicFundamentalGroup
