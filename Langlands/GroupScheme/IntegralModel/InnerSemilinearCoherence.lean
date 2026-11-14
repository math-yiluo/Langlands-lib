import Langlands.GroupScheme.IntegralModel.InnerSemilinearExtension
import Langlands.GroupScheme.IntegralModel.SemilinearCoherence
import Langlands.GroupScheme.Rational.SubgroupConjugacyDescent

/-! # Coherence of inner-twisted coefficient comparisons -/

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.GroupScheme

/-- The two published conventions for pulling back a base section agree. -/
theorem baseChangeSectionHom_eq_baseChangeBasePoint
    {S T : Scheme.{u}} (b : T ⟶ S) (G : GroupScheme S)
    (g : Over.mk (𝟙 S) ⟶ G.X) :
    baseChangeSectionHom b G g = baseChangeBasePoint b G g := rfl

namespace IntegralModel

open GaloisPointComparison Descent

variable (k L : Type u) [Field k] [Field L] [Algebra k L]
  (G : GroupScheme (Spec (CommRingCat.of k)))

/-- The image of the pulled-back base point under the named canonical comparison
is its coefficient conjugate. -/
theorem galoisDescentIso_baseChangeBasePoint (σ : L ≃ₐ[k] L)
    (x : rationalPoints (baseChanged k L G)) :
    baseChangeBasePoint (galoisBaseMap k L σ) (baseChanged k L G) x ≫
        (galoisDescentIso k L G σ).hom.hom.hom =
      rationalConjugate k L G σ x := by
  rw [← baseChangeSectionHom_eq_baseChangeBasePoint]
  change rationalPoints.map (galoisDescentIso k L G σ).hom
    (baseChangeSectionHom (galoisBaseMap k L σ) (baseChanged k L G) x) = _
  exact (DFunLike.congr_fun (galoisDescentIso_map_eq k G σ) _).trans
    (rationalConjugate_eq_transport k L G σ x)

/-- The generic inner-twisted comparisons satisfy the tower law whenever the
conjugators satisfy the crossed-product identity. -/
theorem innerGaloisDescentIso_tower (σ τ υ : L ≃ₐ[k] L)
    (hστ : galoisBaseMap k L σ ≫ galoisBaseMap k L τ = galoisBaseMap k L υ)
    (x y z : rationalPoints (baseChanged k L G))
    (hc : z = x * rationalConjugate k L G σ y) :
    pullbackComparison (galoisBaseMap k L τ) (galoisBaseMap k L σ)
        (galoisBaseMap k L υ) hστ (baseChanged k L G) ≪≫
          innerGaloisDescentIso k G υ z =
      (GroupScheme.baseChange (galoisBaseMap k L σ)).mapIso
        (innerGaloisDescentIso k G τ y) ≪≫ innerGaloisDescentIso k G σ x := by
  apply Iso.ext
  simp only [innerGaloisDescentIso, Iso.trans_hom, Functor.mapIso_hom,
    Functor.map_comp, Category.assoc]
  rw [baseChange_innerIso_hom]
  rw [← Category.assoc
    ((((GroupScheme.baseChange (galoisBaseMap k L σ)).obj (baseChanged k L G)).innerIso
      (baseChangeBasePoint (galoisBaseMap k L σ) (baseChanged k L G) y)).hom)
    (galoisDescentIso k L G σ).hom ((baseChanged k L G).innerIso x).hom]
  rw [innerIso_hom_comp (galoisDescentIso k L G σ).hom]
  rw [galoisDescentIso_baseChangeBasePoint]
  simp only [Category.assoc]
  rw [← innerIso_mul_hom, ← hc]
  have ht := congrArg (fun e => e.hom) (galoisDescentIso_tower k G σ τ υ hστ)
  simp only [Iso.trans_hom, Functor.mapIso_hom] at ht
  rw [← Category.assoc, ht, Category.assoc]

section Integral

variable {L}
  {R : Type u} [CommRing R] [IsDomain R] [Algebra R L] [IsFractionRing R L]
  (P : IntegralModel R L (baseChanged k L G)) {I : Type}
  (a : I → (Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of R))) [∀ i, IsIso (a i)]
  (σ : I → (L ≃ₐ[k] L)) (z : I → rationalPoints (baseChanged k L G))
  (m : I → I → I) (hm : ∀ i j, a i ≫ a j = a (m i j))
  (hv : ∀ i j, galoisBaseMap k L (σ i) ≫ galoisBaseMap k L (σ j) =
    galoisBaseMap k L (σ (m i j)))
  (hc : ∀ i j, z (m i j) = z i * rationalConjugate k L G (σ i) (z j))
  (hvc : ∀ i, galoisBaseMap k L (σ i) ≫ Spec.algebraMap R L =
    Spec.algebraMap R L ≫ a i)
  (hext : HasSmoothHomExtension (R := R) (L := L)) (hP : P.IsSmooth)
  (hstable : ∀ i, ∀ g ∈ P.integralPoints,
    z i * rationalConjugate k L G (σ i) g * (z i)⁻¹ ∈ P.integralPoints)
  (hstable' : ∀ i, ∀ g ∈ P.integralPoints,
    rationalConjugate k L G (σ i).symm ((z i)⁻¹ * g * z i) ∈ P.integralPoints)

include hv hc in
/-- Generic rigidity forces the integral inner-twisted comparisons to obey
the same tower law as their specified generic fibres. -/
theorem innerGaloisTwistIso_tower (i j : I) :
    pullbackComparison (a j) (a i) (a (m i j)) (hm i j) P.group ≪≫
        (innerGaloisTwistIso k G P (σ (m i j)) (z (m i j)) (a (m i j))
          (hvc (m i j)) hext hP (hstable (m i j)) (hstable' (m i j))).iso =
      (GroupScheme.baseChange (a i)).mapIso
        (innerGaloisTwistIso k G P (σ j) (z j) (a j) (hvc j) hext hP
          (hstable j) (hstable' j)).iso ≪≫
        (innerGaloisTwistIso k G P (σ i) (z i) (a i) (hvc i) hext hP
          (hstable i) (hstable' i)).iso :=
  semilinear_tower_of_generic P (a i) (a j) (a (m i j)) (hm i j)
    (galoisBaseMap k L (σ i)) (galoisBaseMap k L (σ j))
    (galoisBaseMap k L (σ (m i j))) (hv i j)
    (hvc i) (hvc j) (hvc (m i j))
    _ _ _ _ _ _
    (innerGaloisTwistIso_generic_comm k G P (σ i) (z i) (a i) (hvc i)
      hext hP (hstable i) (hstable' i))
    (innerGaloisTwistIso_generic_comm k G P (σ j) (z j) (a j) (hvc j)
      hext hP (hstable j) (hstable' j))
    (innerGaloisTwistIso_generic_comm k G P (σ (m i j)) (z (m i j)) (a (m i j))
      (hvc (m i j)) hext hP (hstable (m i j)) (hstable' (m i j)))
    (innerGaloisDescentIso_tower k L G (σ i) (σ j) (σ (m i j)) (hv i j)
      (z i) (z j) (z (m i j)) (hc i j))

variable {B : Scheme.{u}} (p : Spec (CommRingCat.of R) ⟶ B)
  (q : I → (Spec (CommRingCat.of R) ⟶ Overlap p))
  [∀ i, IsIso (q i ≫ fst p)] [Finite I] [IsIso (Sigma.desc q)]
  (hf : ∀ i, q i ≫ fst p = 𝟙 _) (hg : ∀ i, q i ≫ snd p = a i)

/-- Stable inner-twisted points and a supplied extension property produce
coherent integral Čech data on a finite normalized component cover. -/
def datumOfStableInnerGaloisPoints : Datum p P.group :=
  datumOfGenericSemilinear P p q a (fun i => galoisBaseMap k L (σ i)) hf hg m hm hv hvc
    (fun i => (innerGaloisTwistIso k G P (σ i) (z i) (a i) (hvc i) hext hP
      (hstable i) (hstable' i)).iso)
    (fun i => innerGaloisDescentIso k G (σ i) (z i))
    (fun i => innerGaloisTwistIso_generic_comm k G P (σ i) (z i) (a i) (hvc i)
      hext hP (hstable i) (hstable' i))
    (fun i j => innerGaloisDescentIso_tower k L G (σ i) (σ j) (σ (m i j)) (hv i j)
      (z i) (z j) (z (m i j)) (hc i j))

/-- The datum recovers the original integral isomorphism on every supplied
normalized overlap component. -/
theorem pullIso_datumOfStableInnerGaloisPoints (i : I) :
    pullIso (q i) (hf i) (hg i)
        (datumOfStableInnerGaloisPoints k G P a σ z m hm hv hc hvc hext hP
          hstable hstable' p q hf hg).overlap =
      semilinearComponent P.group
        (innerGaloisTwistIso k G P (σ i) (z i) (a i) (hvc i) hext hP
          (hstable i) (hstable' i)).iso :=
  pullIso_datumOfGenericSemilinear P p q a (fun j => galoisBaseMap k L (σ j))
    hf hg m hm hv hvc _ _ _ _ i

end Integral

end IntegralModel
end Langlands.GroupScheme
