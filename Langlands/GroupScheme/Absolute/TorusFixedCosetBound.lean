import Langlands.GroupScheme.FixedCosetFactorization
import Langlands.GroupScheme.Torus.MaximalTransport
import Langlands.GroupScheme.Rational.RelativeRoots
import Langlands.GroupScheme.SchemeAction
import Mathlib.SetTheory.Cardinal.Finite

/-! # Bounding torus-fixed quotient points by the actual Weyl quotient -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
  {G P : GroupScheme (Spec (CommRingCat.of k))}
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  (i : T.toGrp ⟶ G) (j : P ⟶ G) {Q : Over (Spec (CommRingCat.of k))}
  (q : G.X ⟶ Q)
  (hfib : ∀ (V : Over (Spec (CommRingCat.of k))) (g h : V ⟶ G.X),
    g ≫ q = h ≫ q ↔ g⁻¹ * h ∈ (SubgroupFunctor.range j).carrier V)

include hfib

/-- If maximal tori are conjugate inside the stabilizer, a torus-fixed coset
with a rational lift has a normalizer representative in the same coset. -/
theorem exists_normalizer_representative_of_torus_fixed_coset
    (hi : IsMaximalTorus i) (hj : IsClosedSubgroup j)
    (f : T.toGrp ⟶ P) (hf : f ≫ j = i)
    (hconj : MaximalToriAreConjugate P)
    (g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X)
    (hfixed : ∀ (V : Over (Spec (CommRingCat.of k))) (t : V ⟶ T.toGrp.X),
      ((t ≫ i.hom.hom) * G.constantPoint g V) ≫ q = G.constantPoint g V ≫ q) :
    ∃ n : normalizerPoints i, n.val ≫ q = g ≫ q := by
  have := hi.2.1.mono
  have := hj.mono
  have : Mono i.hom.hom := Over.mono_of_mono_left _
  have : Mono j.hom.hom := Over.mono_of_mono_left _
  let f' := factorOfFixedCoset i j q hfib g hfixed
  have hf' : f' ≫ j = i ≫ (G.innerIso g⁻¹).hom :=
    factorOfFixedCoset_comp i j q hfib g hfixed
  have hfmax : IsMaximalTorus f := by
    apply IsMaximalTorus.of_comp hj
    rwa [hf]
  have hf'max : IsMaximalTorus f' := by
    apply IsMaximalTorus.of_comp hj
    rw [hf']
    exact hi.comp_iso (G.innerIso g⁻¹)
  obtain ⟨p, e, he⟩ := hconj T T f f' hfmax hf'max
  let σ : T ≅ T :=
    { hom := Additive.ofMul e.hom
      inv := Additive.ofMul e.inv
      hom_inv_id := congrArg Additive.ofMul e.hom_inv_id
      inv_hom_id := congrArg Additive.ofMul e.inv_hom_id }
  refine ⟨⟨g * (p ≫ j.hom.hom), σ, ?_⟩, ?_⟩
  · change i ≫ (G.innerIso (g * (p ≫ j.hom.hom))).hom = e.hom ≫ i
    calc
      _ = (f ≫ (P.innerIso p).hom) ≫ j ≫ (G.innerIso g).hom := by
        rw [innerIso_mul_hom, ← hf]
        simp only [Category.assoc]
        rw [← Category.assoc j, ← innerIso_hom_comp j p]
        simp only [Category.assoc]
      _ = (e.hom ≫ f') ≫ j ≫ (G.innerIso g).hom := by rw [he]
      _ = e.hom ≫ i := by
        rw [Category.assoc, ← Category.assoc f', hf', innerIso_inv_hom]
        simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  · apply ((hfib _ g (g * (p ≫ j.hom.hom))).mpr ?_).symm
    rw [inv_mul_cancel_left]
    exact SubgroupFunctor.mem_range.mpr ⟨p, rfl⟩

/-- Normalizer representatives define a quotient-point map on `N(k)/Z(k)`
whenever the whole-torus centralizer points belong to the stabilizer. -/
def relativeWeylCosetMap
    (hc : centralizerPoints i ≤
      (SubgroupFunctor.range j).carrier (Over.mk (𝟙 (Spec (CommRingCat.of k))))) :
    relativeWeylGroup i → (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Q) :=
  Quotient.lift (fun n : normalizerPoints i => n.val ≫ q) (by
    intro n n' h
    apply (hfib _ n.val n'.val).mpr
    apply hc
    have heq : (QuotientGroup.mk n : relativeWeylGroup i) = QuotientGroup.mk n' :=
      Quotient.sound h
    have hmem : n⁻¹ * n' ∈ (centralizerPoints i).subgroupOf (normalizerPoints i) :=
      QuotientGroup.eq.mp heq
    exact hmem)

@[simp]
theorem relativeWeylCosetMap_mk
    (hc : centralizerPoints i ≤
      (SubgroupFunctor.range j).carrier (Over.mk (𝟙 (Spec (CommRingCat.of k)))))
    (n : normalizerPoints i) :
    relativeWeylCosetMap i j q hfib hc (QuotientGroup.mk n) = n.val ≫ q :=
  rfl

variable (hi : IsMaximalTorus i) (hj : IsClosedSubgroup j)
  (f : T.toGrp ⟶ P) (hf : f ≫ j = i)
  (hconj : MaximalToriAreConjugate P)
  (hc : centralizerPoints i ≤
    (SubgroupFunctor.range j).carrier (Over.mk (𝟙 (Spec (CommRingCat.of k)))))
  (a : SchemeAction T.toGrp Q)
  (hact : ∀ (V : Over (Spec (CommRingCat.of k)))
    (t : V ⟶ T.toGrp.X) (g : V ⟶ G.X),
    a.act t (g ≫ q) = ((t ≫ i.hom.hom) * g) ≫ q)
  (hsurj : Function.Surjective
    (fun g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X => g ≫ q))

include hi hj f hf hconj hc hact hsurj

/-- Every all-test fixed rational point lies in the image of the actual Weyl
quotient when it has a rational lift. -/
theorem exists_relativeWeylCosetMap_eq_of_isFixed
    (x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Q) (hx : a.IsFixed x) :
    ∃ w : relativeWeylGroup i, relativeWeylCosetMap i j q hfib hc w = x := by
  obtain ⟨g, rfl⟩ := hsurj x
  have hfixed : ∀ (V : Over (Spec (CommRingCat.of k))) (t : V ⟶ T.toGrp.X),
      ((t ≫ i.hom.hom) * G.constantPoint g V) ≫ q = G.constantPoint g V ≫ q := by
    intro V t
    have he := hx V (Over.homMk V.hom (by simp)) t
    rw [← Category.assoc] at he
    change a.act t (G.constantPoint g V ≫ q) = G.constantPoint g V ≫ q at he
    rwa [hact] at he
  obtain ⟨n, hn⟩ := exists_normalizer_representative_of_torus_fixed_coset
    i j q hfib hi hj f hf hconj g hfixed
  exact ⟨QuotientGroup.mk n, hn⟩

/-- All-test fixed rational points embed into the actual Weyl quotient. The
choice of a Weyl preimage is the only noncanonical step. -/
def torusFixedPointWeylEmbedding :
    {x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Q // a.IsFixed x} ↪
      relativeWeylGroup i where
  toFun x := Classical.choose (exists_relativeWeylCosetMap_eq_of_isFixed
    i j q hfib hi hj f hf hconj hc a hact hsurj x.val x.property)
  inj' := by
    intro x y h
    apply Subtype.ext
    have hx := Classical.choose_spec (exists_relativeWeylCosetMap_eq_of_isFixed
      i j q hfib hi hj f hf hconj hc a hact hsurj x.val x.property)
    have hy := Classical.choose_spec (exists_relativeWeylCosetMap_eq_of_isFixed
      i j q hfib hi hj f hf hconj hc a hact hsurj y.val y.property)
    exact hx.symm.trans ((congrArg (relativeWeylCosetMap i j q hfib hc) h).trans hy)

/-- Finiteness of the actual Weyl quotient implies finiteness of all-test fixed
rational points under the geometric hypotheses of the embedding. -/
theorem finite_torusFixedPoints [Finite (relativeWeylGroup i)] :
    Finite {x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Q // a.IsFixed x} :=
  Finite.of_injective
    (torusFixedPointWeylEmbedding i j q hfib hi hj f hf hconj hc a hact hsurj)
    (torusFixedPointWeylEmbedding i j q hfib hi hj f hf hconj hc a hact hsurj).injective

/-- The number of all-test fixed rational points is at most the order of the
actual Weyl quotient. -/
theorem card_torusFixedPoints_le_relativeWeylGroup [Finite (relativeWeylGroup i)] :
    Nat.card {x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Q // a.IsFixed x} ≤
      Nat.card (relativeWeylGroup i) :=
  Nat.card_le_card_of_injective
    (torusFixedPointWeylEmbedding i j q hfib hi hj f hf hconj hc a hact hsurj)
    (torusFixedPointWeylEmbedding i j q hfib hi hj f hf hconj hc a hact hsurj).injective

end Langlands.GroupScheme
