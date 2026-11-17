import Langlands.GroupScheme.Rational.SeparableSolvableRadicalStatement
import Langlands.GroupScheme.Rational.SolvableRadicalBaseChange
import Langlands.GroupScheme.Rational.SolvableRadicalExistenceProof
import Langlands.GroupScheme.Descent.GaloisInvariantClosedSubgroups
import Langlands.GroupScheme.Torus.StrictHenselianMaximalReduction
import Mathlib.FieldTheory.IsSepClosed

/-! # Solvable radicals under separable algebraic field extension: proof -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

namespace SeparableSolvableRadical

/-- Galois case: over a Galois extension `L/k` (of any degree), the base change of a
solvable radical of a smooth connected affine `k`-group is a solvable radical over `L`. -/
theorem isSolvableRadical_baseChange_galois {k L : Type u} [Field k] [Field L]
    [Algebra k L] [IsGalois k L]
    {G R : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    {r : R ⟶ G} (hr : IsSolvableRadical r) :
    IsSolvableRadical
      ((GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k L)))).map r) := by
  let c := Spec.map (CommRingCat.ofHom (algebraMap k L))
  let : Smooth ((GroupScheme.baseChange c).obj G).X.hom := by
    change Smooth (pullback.snd G.X.hom c)
    infer_instance
  let : IsAffineHom ((GroupScheme.baseChange c).obj G).X.hom := by
    change IsAffineHom (pullback.snd G.X.hom c)
    infer_instance
  let : ConnectedSpace ((GroupScheme.baseChange c).obj G).X.left :=
    G.connectedSpace_baseChange_of_smooth_affine c
  obtain ⟨R', r', hr'⟩ := solvableRadicalExistence L ((GroupScheme.baseChange c).obj G)
  obtain ⟨R₀, j, e, -, hj, he⟩ := Descent.GaloisInvariantClosedSubgroup.exists_descent
    hr'.isClosedSubgroup hr'.range_galoisTransport
  have hj' : IsSolvableRadical j := by
    apply IsSolvableRadical.of_baseChange (K := L) (hclosed := hj)
    change IsSolvableRadical ((GroupScheme.baseChange (algebraBaseMap k L)).map j)
    rw [he]
    exact hr'.precomp_iso e
  let f : R ≅ R₀ := hr.iso hj'
  have hf : f.hom ≫ j = r := hr.iso_hom_comp hj'
  have heq : (GroupScheme.baseChange c).map r =
      ((GroupScheme.baseChange c).mapIso f ≪≫ e).hom ≫ r' := by
    rw [← hf, Functor.map_comp]
    change _ ≫ (GroupScheme.baseChange (algebraBaseMap k L)).map j = _
    rw [he]
    simp only [Iso.trans_hom, Functor.mapIso_hom, Category.assoc]
  rw [heq]
  exact hr'.precomp_iso _

/-- Separable algebraic case: base change of a solvable radical along a separable
algebraic extension `K/k` is a solvable radical over `K`. -/
theorem isSolvableRadical_baseChange {k K : Type u} [Field k] [Field K]
    [Algebra k K] [Algebra.IsSeparable k K]
    {G R : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    {r : R ⟶ G} (hr : IsSolvableRadical r) :
    IsSolvableRadical
      ((GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k K)))).map r) := by
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
  have hL : IsSolvableRadical ((GroupScheme.baseChange c).map r) :=
    isSolvableRadical_baseChange_galois (L := SeparableClosure k) hr
  have htotal : IsSolvableRadical ((GroupScheme.baseChange (d ≫ b)).map r) := by
    rw [hcomp]
    exact hL
  have hiter : IsSolvableRadical
      ((GroupScheme.baseChange d).map ((GroupScheme.baseChange b).map r)) := by
    have h := baseChangeCompIso_hom_naturality b d r
    have h' : (GroupScheme.baseChange d).map ((GroupScheme.baseChange b).map r) =
        (baseChangeCompIso b d R).symm.hom ≫
          ((GroupScheme.baseChange (d ≫ b)).map r ≫ (baseChangeCompIso b d G).hom) := by
      rw [h, Iso.symm_hom, Iso.inv_hom_id_assoc]
    rw [h']
    exact (htotal.comp_iso (baseChangeCompIso b d G)).precomp_iso _
  let : IsAffineHom ((GroupScheme.baseChange b).obj G).X.hom := by
    change IsAffineHom (pullback.snd G.X.hom b)
    infer_instance
  exact IsSolvableRadical.of_baseChange (K := SeparableClosure k) hiter
    (hr.isClosedSubgroup.baseChange b)

end SeparableSolvableRadical

open SeparableSolvableRadical in
/-- **Milne, *Algebraic Groups* (2017), Proposition 19.1**: the formation of the
solvable radical commutes with separable algebraic field extension. -/
theorem separableAlgebraicSolvableRadical :
    SeparableAlgebraicSolvableRadicalStatement.{u} := by
  intro k K _ _ _ _ G hs ha hc R r hr
  have := hs
  have := ha
  have := hc
  exact isSolvableRadical_baseChange hr

end Langlands.GroupScheme
