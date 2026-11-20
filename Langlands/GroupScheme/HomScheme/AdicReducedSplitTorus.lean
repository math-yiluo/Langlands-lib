import Langlands.GroupScheme.HomScheme.FiniteSplitTorusGraphDescent
import Langlands.GroupScheme.Descent.DisjointPullbackCoherence
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian

/-! # Split-torus Hom effectivity over a reduced complete local base -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing TopologicalSpace
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.GroupScheme.HomScheme.Adic

open Diagonalizable TorsionDensity

/-- Adic restriction for a split torus over a reduced complete Noetherian
local ring is bijective for smooth separated quasi-compact groups with affine
residue fibres. -/
def ReducedSplitTorusAdicEffectivityStatement : Prop :=
  ∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [_root_.IsReduced A] [IsAdicComplete (maximalIdeal A) A]
    (L : Type u) [Fintype L] (G : GroupScheme (Spec (CommRingCat.of A)))
    [Smooth G.X.hom] [IsSeparated G.X.hom] [QuasiCompact G.X.hom],
    HasAffineResidueFibers G →
    Function.Bijective (System.restrict (maximalIdeal A)
      (groupScheme (CommRingCat.of A) (L → ℤ)).toGrp G)

variable {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
  [_root_.IsReduced A] [IsAdicComplete (maximalIdeal A) A]
  (L : Type u) [Fintype L]
  {G : GroupScheme (Spec (CommRingCat.of A))}
  [Smooth G.X.hom] [IsSeparated G.X.hom] [QuasiCompact G.X.hom]

local notation "S" => Spec (CommRingCat.of A)
local notation "H" => CommGroupScheme.toGrp (groupScheme (CommRingCat.of A) (L → ℤ))

set_option maxHeartbeats 1500000 in
/-- The actual residue-field maps at the minimal primes give a realization over
the product of their fields. Its finite graph image gives descent to the base. -/
theorem System.exists_splitTorus_algebraization_of_isReduced (hG : HasAffineResidueFibers G)
    (s : System (maximalIdeal A) (H) G) : ∃ g : H ⟶ G, System.restrict (maximalIdeal A) H G g = s := by
  classical
  choose f hf using s.exists_splitTorusHom_on_residueField hG L
  let J := ↥(minimalPrimes A)
  let : Finite J := (minimalPrimes.finite_of_isNoetherianRing A).to_subtype
  let y (i : J) : S := ⟨i.1, i.2.isPrime⟩
  let K (i : J) : CommRingCat := Scheme.residueField S (y i)
  let r (i : J) : Spec (K i) ⟶ S := Scheme.fromSpecResidueField S (y i)
  let B := ∀ i : J, K i
  let φi (i : J) : A →+* K i := (Spec.preimage (r i)).hom
  let φ : A →+* B := RingHom.pi φi
  have hker (i : J) : RingHom.ker (φi i) = i.1 := by
    let : IsDomain (K i) := inferInstanceAs (IsDomain (Scheme.residueField S (y i)))
    let p₀ : Spec (K i) := ⟨⊥, Ideal.isPrime_bot⟩
    have h := congrArg (fun k : Spec (K i) ⟶ S => (k p₀).asIdeal) (Spec.map_preimage (r i))
    change (PrimeSpectrum.comap (φi i) p₀).asIdeal = (r i p₀).asIdeal at h
    rw [PrimeSpectrum.comap_asIdeal] at h
    change Ideal.comap (φi i) ⊥ = (Scheme.fromSpecResidueField S (y i) p₀).asIdeal at h
    rwa [Scheme.fromSpecResidueField_apply, ← RingHom.ker_eq_comap_bot] at h
  have hφ : Function.Injective φ := by
    apply (RingHom.injective_iff_ker_eq_bot φ).mpr
    apply eq_bot_iff.mpr
    intro x hx
    have hs : sInf (minimalPrimes A) = (⊥ : Ideal A) := by
      rw [Ideal.sInf_minimalPrimes, Ideal.radical_bot_of_isReduced]
    rw [← hs, Ideal.mem_sInf]
    intro i hi
    have he : RingHom.ker (φi ⟨i, hi⟩) = i := hker ⟨i, hi⟩
    rw [← he, RingHom.mem_ker]
    exact congrFun (RingHom.mem_ker.mp hx) ⟨i, hi⟩
  let b := Spec.map (CommRingCat.ofHom φ)
  let q (i : J) : Spec (K i) ⟶ Spec (CommRingCat.of B) :=
    Spec.map (CommRingCat.ofHom (Pi.evalRingHom (fun i => K i) i))
  let : IsIso (Sigma.desc q) := inferInstanceAs (IsIso (sigmaSpec K))
  have hq (i : J) : q i ≫ b = r i := by
    rw [← Spec.map_comp]
    exact Spec.map_preimage (r i)
  let t (i : J) : Over.mk (r i) ⟶ Over.mk b := Over.homMk (q i) (hq i)
  let comparison (P : GroupScheme S) (i : J) := Descent.pullbackComparison b (q i) (r i) (hq i) P
  let g : RelativeHom H G (Over.mk b) := Descent.DisjointComponents.groupHom q
    (fun i => (comparison H i).hom ≫ f (y i) ≫ (comparison G i).inv)
  have hgi (i : J) : evaluate (t i) g = f (y i) := by
    change (comparison H i).inv ≫ (baseChange (q i)).map g ≫ (comparison G i).hom = _
    simp [g, Category.assoc]
  have hg : s.RealizesSplitTorsion L g := by
    intro n hn
    apply Descent.DisjointComponents.pullHom_ext_along q hq hq
    intro i
    let j := splitTorsionRestriction (CommRingCat.of A) L n
    change evaluate (t i) ((baseChange b).map j ≫ g) =
      evaluate (t i) ((baseChange b).map (s.splitTorsionHom L n hn))
    have hc := Descent.pullHom_comp (t i).left (t i).w (t i).w (t i).w ((baseChange b).map j) g
    change evaluate (t i) ((baseChange b).map j ≫ g) =
      evaluate (t i) ((baseChange b).map j) ≫ evaluate (t i) g at hc
    have hj : evaluate (t i) ((baseChange b).map j) = (baseChange (r i)).map j :=
      evaluate_baseChange (t i) j
    have hs : evaluate (t i) ((baseChange b).map (s.splitTorsionHom L n hn)) =
        (baseChange (r i)).map (s.splitTorsionHom L n hn) :=
      evaluate_baseChange (t i) (s.splitTorsionHom L n hn)
    rw [hc, hj, hs, hgi]
    exact hf (y i) n hn
  let : ∀ i : J, IsNoetherianRing (K i) := fun i =>
    inferInstanceAs (IsNoetherianRing (Scheme.residueField S (y i)))
  let : IsNoetherianRing B := inferInstanceAs (IsNoetherianRing (∀ i : J, K i))
  let : AddGroup.FG (L → ℤ) := Module.Finite.iff_addGroup_fg.mp inferInstance
  let : IsNoetherianRing (AddMonoidAlgebra B (L → ℤ)) :=
    Algebra.FiniteType.isNoetherianRing B _
  let e : ((baseChange b).obj H).X.left ≅ Spec (CommRingCat.of (AddMonoidAlgebra B (L → ℤ))) :=
    ((Grp.forget _) ⋙ Over.forget _).mapIso (baseChangeIso b (L → ℤ))
  let : NoetherianSpace ((baseChange (Over.mk b).hom).obj H).X.left :=
    (Scheme.homeoOfIso e).isInducing.noetherianSpace
  have hfin := s.hasFiniteSplitTorusGraphImages hG f hf (relativeGraphMap g)
    (s.range_relativeGraphMap_subset_residueGraphSections hf hg)
  obtain ⟨a, ha, _⟩ := existsUnique_hom_of_finite_graph_image L φ hφ g hfin
    (fun n hn => ⟨s.splitTorsionHom L n hn, (hg n hn).symm⟩)
  have hH : RelativeMultiplicativeType.IsMultiplicativeType H :=
    .of_isDiagonalizable (isDiagonalizable_groupScheme (CommRingCat.of A) (L → ℤ))
  refine ⟨a, (s.restrict_eq_iff_torsionRestriction hH a).mpr ?_⟩
  intro n hn
  let D := (groupScheme (CommRingCat.of A) ((L → ℤ) ⧸ multiples (L → ℤ) n)).toGrp
  let j := splitTorsionRestriction (CommRingCat.of A) L n
  let d := torsionIso (CommRingCat.of A) (L → ℤ) n
  have hd : d.inv ≫ torsionι H (n : ℤ) = j := torsionIso_inv_comp_ι _ _ _
  let : IsSchemeTheoreticallyDominant b := isSchemeTheoreticallyDominant_specMap hφ
  have ht : j ≫ a = s.splitTorsionHom L n hn := by
    apply SchematicHomEquality.baseChange_hom_ext b
    rw [Functor.map_comp, ha]
    exact hg n hn
  let : IsFinite D.X.hom := isFinite_splitTorsion L n hn
  let : IsFinite (torsion H (n : ℤ)).X.hom := (hH.torsion_geometry n hn).1
  have hc := s.finiteRestriction_comp (torsionι H (n : ℤ)) d.inv j hd
  apply (cancel_epi d.inv).mp
  rw [← Category.assoc, hd, ht]
  exact hc.symm

/-- The maximal-ideal quotient comparison is bijective on this reduced base. -/
theorem reducedSplitTorusAdicEffectivity : ReducedSplitTorusAdicEffectivityStatement.{u} := by
  intro A _ _ _ _ _ L _ G _ _ _ hG
  let : AddGroup.FG (L → ℤ) := Module.Finite.iff_addGroup_fg.mp inferInstance
  have hH := RelativeMultiplicativeType.IsMultiplicativeType.of_isDiagonalizable
    (isDiagonalizable_groupScheme (CommRingCat.of A) (L → ℤ))
  exact ⟨System.restrict_injective_of_torsion hH G,
    fun s => s.exists_splitTorus_algebraization_of_isReduced L hG⟩

end Langlands.GroupScheme.HomScheme.Adic
