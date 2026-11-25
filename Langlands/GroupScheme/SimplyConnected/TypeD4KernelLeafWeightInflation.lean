import Langlands.GroupScheme.SimplyConnected.TypeD4KernelLeafFactors
import Langlands.GroupScheme.SimplyConnected.StarOrbitWeights
import Langlands.GroupScheme.Reductive.SplitLeviGluingSimpleGeneration

/-! # Inflation of the actual fundamental weight of a D4 kernel leaf -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.TitsIndexData.AnisotropicKernelIndex

private theorem two_nsmul_fundamentalWeight_eq_root
    {J X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
    (P : RootDatum J X Y) (B : P.Base) (hspan : P.corootSpan ℤ = ⊤)
    (a : B.support) (hcartan : ∀ b : B.support, b ≠ a → P.pairing a.val b.val = 0) :
    (2 : ℕ) • Langlands.RootDatum.fundamentalWeightBasis P B hspan a = P.root a.val := by
  classical
  apply IntegralWeylVector.eq_of_pairing_simple_eq P B hspan
  intro b
  rw [map_nsmul, LinearMap.smul_apply, Langlands.RootDatum.fundamentalWeightBasis_pairing,
    P.root_coroot_eq_pairing]
  by_cases h : b = a
  · subst b
    rw [ite_eq_left rfl, ← P.root_coroot_eq_pairing, P.root_coroot_two]
    norm_num
  · rw [ite_eq_right h, hcartan b h]
    simp

private theorem weightInflation_eq_of_doubled_weights
    {E L : Type u} [Field E] [Field L] [Algebra E L]
    {G H : GroupScheme (Spec (CommRingCat.of E))}
    [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
    {P : GaloisPinningData E L G} {Q : GaloisPinningData E L H}
    (F : P.FactorProjection Q) (b : Q.base.support)
    (x : characterLattice Q.toSplitPinning.torus)
    (y : characterLattice P.toSplitPinning.torus)
    (hx : (2 : ℕ) • x = Q.rootDatum.root b.val)
    (hy : (2 : ℕ) • y = P.rootDatum.root (F.vertices b).val) :
    F.weightInflation x = y := by
  let : IsAddTorsionFree (characterLattice P.toSplitPinning.torus) :=
    LeviGluing.isAddTorsionFree_of_rootDatum P.rootDatum
  have : HasUniqueDiv (characterLattice P.toSplitPinning.torus) :=
    ⟨fun _ hn a b hab => eq_of_nsmul_eq_nsmul_of_addCommute hn (AddCommute.all a b) hab⟩
  apply nsmul_right_injective (n := 2) (by decide)
  calc
    _ = F.weightInflation ((2 : ℕ) • x) := (map_nsmul F.weightInflation 2 x).symm
    _ = F.weightInflation (Q.rootDatum.root b.val) := congrArg F.weightInflation hx
    _ = P.rootDatum.root (F.vertices b).val := F.root_eq b
    _ = _ := hy.symm

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  {d : TitsIndexData G} (p : d.AnisotropicKernelIndex) (hsc : IsSimplyConnected G)

include hsc in
private theorem geometricSimplyConnected :
    IsSimplyConnected ((GroupScheme.baseChange
      (algebraBaseMap k (SeparableClosure k))).obj p.kernel) :=
  isSimplyConnectedFieldExtension k (SeparableClosure k) p.kernel (p.isSimplyConnected hsc)

private abbrev geometricProduct := (p.geometricSimplyConnected hsc).almostSimpleProduct

private abbrev geometricSemisimple := (p.geometricSimplyConnected hsc).isSemisimple

local instance leafKernelSmooth : Smooth p.kernel.X.hom :=
  p.index.isSemisimple.isConnectedReductive.smooth

local instance geometricLeafKernelSmooth :
    Smooth ((GroupScheme.baseChange (algebraBaseMap k (SeparableClosure k))).obj
      p.kernel).X.hom := by
  change Smooth (CategoryTheory.Limits.pullback.snd p.kernel.X.hom _)
  infer_instance

attribute [local instance] SimplyConnectedAlmostSimpleProduct.factorStabilizerDescent_isAffine
  SimplyConnectedAlmostSimpleProduct.factorStabilizerDescent_locallyOfFiniteType

/-- The actual descended pinning with the projection of the original kernel
over its exact component field. -/
def descendedComponentProjection (a : p.index.Vertex) :
    type_of% (Classical.choice (p.index.nonempty_descendedComponentPinningWithProjection
      (p.geometricProduct hsc) (p.geometricSemisimple hsc) (p.isSimplyConnected hsc) a)) :=
  Classical.choice (p.index.nonempty_descendedComponentPinningWithProjection
    (p.geometricProduct hsc) (p.geometricSemisimple hsc) (p.isSimplyConnected hsc) a)

variable (q : d.Vertex ≃ Fin 4)
  (hq : d.IsNumberingOf (CartanMatrix.D 4) (fun i => i.val = 1) q)

include hq in
private theorem weightInflation_componentProjection_D4 (a : p.index.Vertex)
    {E : IntermediateField k (SeparableClosure k)}
    {S : GaloisPinningData.ScalarExtension (E := E) p.index.pinning}
    {H : GroupScheme (Spec (CommRingCat.of E))}
    [IsAffineHom H.X.hom] [LocallyOfFiniteType H.X.hom]
    {j : H ⟶ (GroupScheme.baseChange (algebraBaseMap k E)).obj p.kernel}
    (C : p.index.ComponentPinningWithProjection E a S j)
    (b : C.comparison.pinning.base.support)
    (hspan : C.comparison.pinning.rootDatum.corootSpan ℤ = ⊤) :
    C.projection.weightInflation
        (Langlands.RootDatum.fundamentalWeightBasis C.comparison.pinning.rootDatum
          C.comparison.pinning.base hspan b) =
      S.rootEquiv.weightEquiv (p.index.absoluteFundamentalCharacter (p.isSimplyConnected hsc) a) := by
  let F := C.comparison.pinning
  have hvertex (c : F.base.support) : (C.comparison.vertices c).val = a :=
    ((p.cartanConnected_iff_eq_D4_central_mark q hq _ _).mp
      (C.comparison.vertices c).property).symm
  have hsingleton (c : F.base.support) : c = b := by
    apply C.comparison.vertices.injective
    apply Subtype.ext
    exact (hvertex c).trans (hvertex b).symm
  have hF (c : F.base.support) (hc : c ≠ b) :
      F.rootDatum.pairing b.val c.val = 0 := (hc (hsingleton c)).elim
  have hP (v : p.index.Vertex) (hv : v ≠ a) : p.index.cartan a v = 0 := by
    rw [p.cartan_D4_central_mark q hq, ite_eq_right]
    exact fun h => hv ((p.d4LeafNumbering q hq).injective h).symm
  have hω : (2 : ℕ) • p.index.absoluteFundamentalCharacter (p.isSimplyConnected hsc) a =
      p.index.pinning.rootDatum.root a.val :=
    two_nsmul_fundamentalWeight_eq_root p.index.pinning.rootDatum p.index.pinning.base
      (p.index.pinning_corootSpan_eq_top (p.isSimplyConnected hsc)) a hP
  have hv : C.projection.vertices b =
      (S.rootEquiv.indexEquiv.subtypeEquiv S.base_eq) a := by
    rw [C.vertices_eq b, hvertex b]
  have hω' : (2 : ℕ) •
      S.rootEquiv.weightEquiv (p.index.absoluteFundamentalCharacter (p.isSimplyConnected hsc) a) =
      S.pinning.rootDatum.root (C.projection.vertices b).val := by
    calc
      _ = S.rootEquiv.weightEquiv
          ((2 : ℕ) • p.index.absoluteFundamentalCharacter (p.isSimplyConnected hsc) a) :=
        (S.rootEquiv.weightEquiv.toLinearMap.toAddMonoidHom.map_nsmul 2 _).symm
      _ = S.rootEquiv.weightEquiv (p.index.pinning.rootDatum.root a.val) :=
        congrArg S.rootEquiv.weightEquiv hω
      _ = S.pinning.rootDatum.root (S.rootEquiv.indexEquiv a.val) :=
        RootPairing.Hom.root_weightMap_apply _ _ a.val S.rootEquiv.toHom
      _ = _ := congrArg (fun v : S.pinning.base.support => S.pinning.rootDatum.root v.val) hv.symm
  exact weightInflation_eq_of_doubled_weights C.projection b _ _
    (two_nsmul_fundamentalWeight_eq_root F.rootDatum F.base hspan b hF) hω'

include hq in
/-- For a centrally marked D4 diagram, the fundamental weight of the actual
selected leaf factor inflates to the corresponding original kernel fundamental
weight under the scalar-extension comparison. -/
theorem weightInflation_descendedComponent_D4 (a : p.index.Vertex)
    (b : (p.descendedComponentProjection hsc a).comparison.pinning.base.support)
    (hspan : (p.descendedComponentProjection hsc a).comparison.pinning.rootDatum.corootSpan ℤ = ⊤) :
    type_of% (p.weightInflation_componentProjection_D4 hsc q hq a
      (p.descendedComponentProjection hsc a) b hspan) :=
  p.weightInflation_componentProjection_D4 hsc q hq a (p.descendedComponentProjection hsc a) b hspan

end Langlands.GroupScheme.TitsIndexData.AnisotropicKernelIndex
