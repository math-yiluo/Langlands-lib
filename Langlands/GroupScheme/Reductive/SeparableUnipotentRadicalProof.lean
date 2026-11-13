import Langlands.GroupScheme.Reductive.SeparableUnipotentRadicalStatement
import Langlands.GroupScheme.Reductive.GaloisRadicalDescent
import Langlands.GroupScheme.Reductive.PseudoReductiveSeparableExtensionProof
import Langlands.GroupScheme.Reductive.SemisimpleFieldReflectionProof
import Langlands.GroupScheme.Reductive.UnipotentRadicalExistenceProof
import Langlands.GroupScheme.Rational.UnipotentRadicalProperties
import Langlands.GroupScheme.Rational.PseudoParabolicAmbientTransport
import Langlands.GroupScheme.Rational.MinimalPseudoParabolicRangeReduction
import Langlands.GroupScheme.Torus.StrictHenselianMaximalReduction
import Mathlib.FieldTheory.IsSepClosed

/-! # Unipotent radicals under separable algebraic field extension: proof -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

namespace SeparableUnipotentRadical

/-- Galois case: over a Galois extension `L/k` (of any degree), the base change of a
`k`-unipotent radical of a smooth connected affine `k`-group is an `L`-unipotent radical. -/
theorem isUnipotentRadical_baseChange_galois {k L : Type u} [Field k] [Field L]
    [Algebra k L] [IsGalois k L]
    {G U : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    {i : U ⟶ G} (hi : IsUnipotentRadical i) :
    IsUnipotentRadical
      ((GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k L)))).map i) := by
  let c := Spec.map (CommRingCat.ofHom (algebraMap k L))
  let : Smooth ((GroupScheme.baseChange c).obj G).X.hom := by
    change Smooth (pullback.snd G.X.hom c)
    infer_instance
  let : IsAffineHom ((GroupScheme.baseChange c).obj G).X.hom := by
    change IsAffineHom (pullback.snd G.X.hom c)
    infer_instance
  let : ConnectedSpace ((GroupScheme.baseChange c).obj G).X.left :=
    G.connectedSpace_baseChange_of_smooth_affine c
  obtain ⟨U', i', hi'⟩ := unipotentRadicalExistence L ((GroupScheme.baseChange c).obj G)
  let d := hi'.galoisRadicalDescent
  have hr : SubgroupFunctor.range i = SubgroupFunctor.range d.inclusion :=
    hi.range_eq d.isRadical
  let e : U ≅ d.source :=
    hi.isClosedSubgroup.sourceIsoOfRangeEq d.isRadical.isClosedSubgroup hr
  have he : e.hom ≫ d.inclusion = i :=
    hi.isClosedSubgroup.sourceIsoOfRangeEq_hom_comp d.isRadical.isClosedSubgroup hr
  have heq : (GroupScheme.baseChange c).map i =
      ((GroupScheme.baseChange c).mapIso e ≪≫ d.comparison).hom ≫ i' := by
    rw [← he, Functor.map_comp]
    change _ ≫ (GroupScheme.baseChange (algebraBaseMap k L)).map d.inclusion = _
    rw [d.recovers]
    simp only [Iso.trans_hom, Functor.mapIso_hom, Category.assoc]
  rw [heq]
  exact hi'.precomp_iso _

/-- Part 1 of the target: base change of a `k`-unipotent radical along a separable
algebraic extension `K/k` is a `K`-unipotent radical. -/
theorem isUnipotentRadical_baseChange {k K : Type u} [Field k] [Field K]
    [Algebra k K] [Algebra.IsSeparable k K]
    {G U : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    {i : U ⟶ G} (hi : IsUnipotentRadical i) :
    IsUnipotentRadical
      ((GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k K)))).map i) := by
  let b := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let ι : K →ₐ[k] SeparableClosure k := IsSepClosed.lift
  let : Algebra K (SeparableClosure k) := ι.toRingHom.toAlgebra
  let c := Spec.map (CommRingCat.ofHom (algebraMap k (SeparableClosure k)))
  let d := Spec.map (CommRingCat.ofHom (algebraMap K (SeparableClosure k)))
  have hcomp : d ≫ b = c := by
    dsimp [b, c, d]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    apply congrArg (fun f => Spec.map (CommRingCat.ofHom f))
    exact RingHom.ext fun x => ι.commutes x
  have hL : IsUnipotentRadical ((GroupScheme.baseChange c).map i) :=
    isUnipotentRadical_baseChange_galois (L := SeparableClosure k) hi
  have htotal : IsUnipotentRadical ((GroupScheme.baseChange (d ≫ b)).map i) := by
    rw [hcomp]
    exact hL
  have hiter : IsUnipotentRadical
      ((GroupScheme.baseChange d).map ((GroupScheme.baseChange b).map i)) := by
    have h := baseChangeCompIso_hom_naturality b d i
    have h' : (GroupScheme.baseChange d).map ((GroupScheme.baseChange b).map i) =
        (baseChangeCompIso b d U).symm.hom ≫
          ((GroupScheme.baseChange (d ≫ b)).map i ≫ (baseChangeCompIso b d G).hom) := by
      rw [h, Iso.symm_hom, Iso.inv_hom_id_assoc]
    rw [h']
    exact (htotal.comp_iso (baseChangeCompIso b d G)).precomp_iso _
  let : IsAffineHom ((GroupScheme.baseChange b).obj G).X.hom := by
    change IsAffineHom (pullback.snd G.X.hom b)
    infer_instance
  exact IsUnipotentRadical.of_baseChange (K := SeparableClosure k) hiter
    (hi.isClosedSubgroup.baseChange b)

end SeparableUnipotentRadical

open SeparableUnipotentRadical in
/-- **CGP Proposition 1.1.9(1)**, separable algebraic case. -/
theorem separableAlgebraicUnipotentRadical :
    SeparableAlgebraicUnipotentRadicalStatement.{u} := by
  intro k K _ _ _ _ G hs ha hc
  have := hs
  have := ha
  have := hc
  refine ⟨fun U i hi => isUnipotentRadical_baseChange hi, ⟨fun hG => ?_, fun hG => ?_⟩⟩
  · exact pseudoReductiveSeparableExtension k K G hG
  · exact ⟨hs, ha, hc, HasTrivialUnipotentRadical.of_fieldExtension
      (K := K) hG.hasTrivialUnipotentRadical⟩

end Langlands.GroupScheme
