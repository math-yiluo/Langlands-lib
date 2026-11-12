import Langlands.GroupScheme.Reductive.StarAction
import Langlands.GroupScheme.Reductive.FieldExtensionProof
import Langlands.GroupScheme.Reductive.RootDatumExistence
import Langlands.GroupScheme.Reductive.RootPinningFromSplitTorus
import Langlands.GroupScheme.Reductive.PinningConstruction
import Langlands.GroupScheme.Torus.ExistenceProof
import Langlands.GroupScheme.Torus.FiniteGaloisSplittingProof
import Langlands.GroupScheme.Torus.MaximalBaseChangeProof
import Langlands.AbelianScheme.Tate.BaseChangeCoherence
import Mathlib.FieldTheory.IsSepClosed

/-! # Galois pinning data for every connected reductive group, and the absolute star action -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

namespace GaloisPinningData

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom]

/-- Galois pinning data from a maximal torus over `k` and a field over which it splits. -/
private def ofSplittingField (hG : IsConnectedReductive G)
    (T : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ G) (hi : IsMaximalTorus i)
    (E : Type u) [Field E] [Algebra k E]
    (hsplit : IsSplitTorus ((CommGroupScheme.baseChange (algebraBaseMap k E)).obj T).toGrp) :
    GaloisPinningData k E G := by
  have := hG.smooth
  have hGE := connectedReductiveFieldExtensionStatement k E G hG
  have hiE := (maximalTorusBaseChange k E G T i hi.1 hi.2.1).mp hi
  have hroot := rootDatumExistence E _ hGE _ hsplit _ hiE
  let J := hroot.choose
  have hJ : Finite J := hroot.choose_spec.choose
  let P := hroot.choose_spec.choose_spec.choose
  have hP := hroot.choose_spec.choose_spec.choose_spec.1
  have hred : P.IsReduced := hroot.choose_spec.choose_spec.choose_spec.2
  exact
    { torus := T
      inclusion := i
      isConnectedReductive := hGE
      isSplitTorus := hsplit
      isMaximalTorus := hiE
      rootIndex := J
      rootDatum := P
      isRootDatum := hP
      isReduced := hred
      base := Langlands.LinearAlgebra.RootDatumBase.base P
      pinning := RootPinning.ofSplitMaximalTorus hGE hsplit _ hiE P hP
        (Langlands.LinearAlgebra.RootDatumBase.base P) }

/-- A maximal torus of `G` defined over `k` splits over the separable closure of `k`. -/
theorem isSplitTorus_separableClosure (T : CommGroupScheme (Spec (CommRingCat.of k)))
    (hT : IsTorus T.toGrp) :
    IsSplitTorus
      ((CommGroupScheme.baseChange (algebraBaseMap k (SeparableClosure k))).obj T).toGrp := by
  obtain ⟨K, _, _, _, _, hsplitK⟩ := torusFiniteGaloisSplitting k T.toGrp hT
  let φ : K →ₐ[k] SeparableClosure k := IsSepClosed.lift
  let c : Spec (CommRingCat.of (SeparableClosure k)) ⟶ Spec (CommRingCat.of K) :=
    Spec.map (CommRingCat.ofHom φ.toRingHom)
  have hc : c ≫ Spec.map (CommRingCat.ofHom (algebraMap k K)) =
      algebraBaseMap k (SeparableClosure k) := by
    simp only [c, algebraBaseMap, ← Spec.map_comp]
    congr 1
    ext x
    exact congrArg Subtype.val (φ.commutes x)
  rw [← hc]
  exact IsSplitTorus.of_iso
    (GroupScheme.baseChangeCompIso (Spec.map (CommRingCat.ofHom (algebraMap k K))) c T.toGrp)
    (hsplitK.baseChange c)

/-- Galois pinning data of a connected reductive group over the separable closure of `k`,
built from a chosen maximal torus over `k`. -/
def ofSeparableClosure (hG : IsConnectedReductive G) :
    GaloisPinningData k (SeparableClosure k) G :=
  have := hG.smooth
  have hT := maximalTorusExistence k G
  ofSplittingField hG hT.choose hT.choose_spec.choose hT.choose_spec.choose_spec
    (SeparableClosure k)
    (isSplitTorus_separableClosure hT.choose hT.choose_spec.choose_spec.1)

/-- Galois pinning data exist over some finite Galois extension of `k`. -/
theorem exists_finiteGalois (hG : IsConnectedReductive G) :
    ∃ (E : Type u) (_ : Field E) (_ : Algebra k E), FiniteDimensional k E ∧ IsGalois k E ∧
      Nonempty (GaloisPinningData k E G) := by
  have := hG.smooth
  obtain ⟨T, i, hi⟩ := maximalTorusExistence k G
  obtain ⟨E, _, _, hfin, hgal, hsplit⟩ := torusFiniteGaloisSplitting k T.toGrp hi.1
  exact ⟨E, inferInstance, inferInstance, hfin, hgal, ⟨ofSplittingField hG T i hi E hsplit⟩⟩

end GaloisPinningData

/-- The absolute star action of a connected reductive group `G` over `k`: the star action of
`Gal(k_s/k)` on the based root datum of `G_{k_s}`, for the Galois pinning data
`GaloisPinningData.ofSeparableClosure`. -/
def absoluteStarAction {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] (hG : IsConnectedReductive G) :
    (SeparableClosure k ≃ₐ[k] SeparableClosure k) →*
      (GaloisPinningData.ofSeparableClosure hG).toSplitPinning.basedRootDatumAut :=
  (GaloisPinningData.ofSeparableClosure hG).starAction

end Langlands.GroupScheme
