import Langlands.GroupScheme.HomScheme.FiniteSourceAdicHom
import Langlands.GroupScheme.Torus.RelativeMultiplicativeTypeTorsion
import Langlands.GroupScheme.Torus.MultiplicativeTypeTorsionDeterminationProof

/-! # Algebraized torsion restrictions of adic Hom systems -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.MonObj
open Langlands.AlgebraicGeometry.AdicAffinePoints

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.GroupScheme

variable {S : Scheme.{u}} {H : GroupScheme S} [IsCommMonObj H.X]

private theorem torsionι_multiplication_of_dvd {m n : ℕ} (h : m ∣ n) :
    torsionι H (m : ℤ) ≫ multiplication H (n : ℤ) = 1 := by
  obtain ⟨d, rfl⟩ := h
  rw [Nat.cast_mul, multiplication_mul, ← Category.assoc, torsionι_multiplication, MonObj.one_comp]

/-- The inclusion from the `m`-torsion into the `n`-torsion for `m ∣ n`. -/
def torsionInclusionOfDvd {m n : ℕ} (h : m ∣ n) : torsion H (m : ℤ) ⟶ torsion H (n : ℤ) :=
  pullback.lift (torsionι H (m : ℤ)) (pullback.snd (multiplication H (m : ℤ)) (kernelUnit H)) <| by
    rw [torsionι_multiplication_of_dvd h, ← pullback.condition]
    exact (torsionι_multiplication (G := H) (m : ℤ)).symm

@[reassoc (attr := simp)] theorem torsionInclusionOfDvd_ι {m n : ℕ} (h : m ∣ n) :
    torsionInclusionOfDvd (H := H) h ≫ torsionι H (n : ℤ) = torsionι H (m : ℤ) :=
  pullback.lift_fst _ _ _

/-- The actual positive integer torsion inclusions detect equality of
homomorphisms from a relative group of multiplicative type. -/
theorem hom_eq_of_torsion_restrictions {G : GroupScheme S}
    (hH : RelativeMultiplicativeType.IsMultiplicativeType H) (f g : H ⟶ G)
    (h : ∀ n : ℕ, 0 < n → torsionι H (n : ℤ) ≫ f = torsionι H (n : ℤ) ≫ g) : f = g := by
  apply (multiplicativeTypeTorsionDetermination S).1 H G hH f g
  intro n hn T x hx
  obtain ⟨y, hy, -⟩ := (existsUnique_torsion_lift_iff H (n : ℤ) T x).mpr (by simpa using hx)
  rw [← hy, Category.assoc, Category.assoc, ← Grp.comp_hom_hom, ← Grp.comp_hom_hom, h n hn]

namespace HomScheme.Adic.System

variable {A : Type u} [CommRing A] {I : Ideal A}
  {K H G : GroupScheme (Spec (CommRingCat.of A))}

/-- Precompose a formal Hom system with an actual homomorphism of sources. -/
def precompose (s : System I H G) (a : K ⟶ H) : System I K G where
  hom n := (baseChange (quotientMap I n)).map a ≫ s.hom n
  compatible n := by
    let b := transitionOver I n
    have h := Descent.pullHom_comp b.left b.w b.w b.w
      ((baseChange (quotientMap I (n + 1))).map a) (s.hom (n + 1))
    change evaluate b ((baseChange (quotientMap I (n + 1))).map a ≫ s.hom (n + 1)) =
      evaluate b ((baseChange (quotientMap I (n + 1))).map a) ≫ evaluate b (s.hom (n + 1)) at h
    have ha : evaluate b ((baseChange (quotientMap I (n + 1))).map a) =
        (baseChange (quotientMap I n)).map a := evaluate_baseChange b a
    have hs : evaluate b (s.hom (n + 1)) = s.hom n := s.compatible n
    rw [ha, hs] at h
    exact h

variable [IsLocalRing A] [IsNoetherianRing A] [IsAdicComplete (maximalIdeal A) A]

/-- The actual map obtained from restricting a formal system to a finite source. -/
def finiteRestriction [IsFinite K.X.hom] (s : System (maximalIdeal A) H G) (a : K ⟶ H) : K ⟶ G :=
  ((finiteSourceAdicHom A K G).surjective (s.precompose a)).choose

/-- Its reductions are precisely the restrictions of the formal system. -/
theorem finiteRestriction_reduce [IsFinite K.X.hom] (s : System (maximalIdeal A) H G)
    (a : K ⟶ H) (n : ℕ) :
    (baseChange (quotientMap (maximalIdeal A) n)).map (s.finiteRestriction a) =
      (baseChange (quotientMap (maximalIdeal A) n)).map a ≫ s.hom n :=
  congrArg (fun v : System (maximalIdeal A) K G => v.hom n)
    ((finiteSourceAdicHom A K G).surjective (s.precompose a)).choose_spec

/-- Two finite restrictions are compatible with every map of finite sources
whose triangles to the original source commute. -/
theorem finiteRestriction_comp {L : GroupScheme (Spec (CommRingCat.of A))}
    [IsFinite K.X.hom] [IsFinite L.X.hom] (s : System (maximalIdeal A) H G)
    (a : K ⟶ H) (b : L ⟶ K) (c : L ⟶ H) (h : b ≫ a = c) :
    b ≫ s.finiteRestriction a = s.finiteRestriction c := by
  apply (finiteSourceAdicHom A L G).injective
  apply System.ext
  intro n
  rw [System.restrict_hom, System.restrict_hom, Functor.map_comp, finiteRestriction_reduce,
    finiteRestriction_reduce, ← Category.assoc, ← Functor.map_comp, h]

variable [IsCommMonObj H.X] (hH : RelativeMultiplicativeType.IsMultiplicativeType H)

/-- Actual algebraized restrictions on all positive integer torsion. -/
def torsionRestriction (s : System (maximalIdeal A) H G) (n : ℕ) (hn : 0 < n) :
    torsion H (n : ℤ) ⟶ G :=
  letI : IsFinite (torsion H (n : ℤ)).X.hom := (hH.torsion_geometry n hn).1
  s.finiteRestriction (torsionι H (n : ℤ))

/-- The native restriction to torsion has the prescribed reduction at every level. -/
theorem torsionRestriction_reduce (s : System (maximalIdeal A) H G) (n : ℕ) (hn : 0 < n)
    (d : ℕ) :
    (baseChange (quotientMap (maximalIdeal A) d)).map (s.torsionRestriction hH n hn) =
      (baseChange (quotientMap (maximalIdeal A) d)).map (torsionι H (n : ℤ)) ≫ s.hom d := by
  have : IsFinite (torsion H (n : ℤ)).X.hom := (hH.torsion_geometry n hn).1
  exact s.finiteRestriction_reduce _ _

/-- The actual restrictions commute with divisibility inclusions of torsion. -/
theorem torsionRestriction_dvd (s : System (maximalIdeal A) H G)
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (h : m ∣ n) :
    torsionInclusionOfDvd h ≫ s.torsionRestriction hH n hn = s.torsionRestriction hH m hm := by
  have : IsFinite (torsion H (m : ℤ)).X.hom := (hH.torsion_geometry m hm).1
  have : IsFinite (torsion H (n : ℤ)).X.hom := (hH.torsion_geometry n hn).1
  exact s.finiteRestriction_comp _ _ _ (torsionInclusionOfDvd_ι h)

set_option maxHeartbeats 1200000 in
/-- Recovering a given formal system is equivalent to recovering its
algebraized restrictions on all positive torsion. -/
theorem restrict_eq_iff_torsionRestriction (s : System (maximalIdeal A) H G) (f : H ⟶ G) :
    System.restrict (maximalIdeal A) H G f = s ↔
      ∀ (n : ℕ) (hn : 0 < n), torsionι H (n : ℤ) ≫ f = s.torsionRestriction hH n hn := by
  constructor
  · intro hf n hn
    have : IsFinite (torsion H (n : ℤ)).X.hom := (hH.torsion_geometry n hn).1
    apply (finiteSourceAdicHom A _ G).injective
    apply System.ext
    intro d
    rw [System.restrict_hom, System.restrict_hom, Functor.map_comp, torsionRestriction_reduce]
    exact congrArg (fun v => (baseChange (quotientMap (maximalIdeal A) d)).map (torsionι H (n : ℤ)) ≫
      v.hom d) hf
  · intro hf
    apply System.ext
    intro d
    let r := quotientMap (maximalIdeal A) d
    let B := baseChange r
    change B.map f = s.hom d
    apply hom_eq_of_torsion_restrictions (hH.baseChange r)
    intro n hn
    have he := congrArg (fun k => B.map k) (hf n hn)
    rw [Functor.map_comp, torsionRestriction_reduce] at he
    let e := torsionBaseChangeIso r H (n : ℤ)
    have hc : e.hom ≫ torsionι (B.obj H) (n : ℤ) = B.map (torsionι H (n : ℤ)) :=
      torsionBaseChangeIso_hom_ι r H (n : ℤ)
    apply (cancel_epi e.hom).mp
    rw [← Category.assoc, hc, ← Category.assoc, hc]
    exact he

include hH in
/-- Adic restriction is injective for sources of multiplicative type over a
complete noetherian local ring and arbitrary targets. -/
theorem restrict_injective_of_torsion (G : GroupScheme (Spec (CommRingCat.of A))) :
    Function.Injective (System.restrict (maximalIdeal A) H G) := by
  intro f g h
  apply hom_eq_of_torsion_restrictions hH
  intro n hn
  let s := System.restrict (maximalIdeal A) H G g
  exact ((restrict_eq_iff_torsionRestriction hH s f).mp h n hn).trans
    (((restrict_eq_iff_torsionRestriction hH s g).mp rfl n hn).symm)

end HomScheme.Adic.System

namespace HomScheme.Adic

/-- Algebraized finite torsion restrictions are coherent and determine recovery
of a formal system from a relative multiplicative-type source. -/
def AdicTorsionRecoveryStatement : Prop :=
  ∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [IsAdicComplete (maximalIdeal A) A]
    (H G : GroupScheme (Spec (CommRingCat.of A))) [IsCommMonObj H.X]
    (hH : RelativeMultiplicativeType.IsMultiplicativeType H)
    (s : System (maximalIdeal A) H G),
    (∀ (m n : ℕ) (hm : 0 < m) (hn : 0 < n) (h : m ∣ n),
      torsionInclusionOfDvd h ≫ s.torsionRestriction hH n hn = s.torsionRestriction hH m hm) ∧
    (∀ f : H ⟶ G, System.restrict (maximalIdeal A) H G f = s ↔
      ∀ (n : ℕ) (hn : 0 < n), torsionι H (n : ℤ) ≫ f = s.torsionRestriction hH n hn)

theorem adicTorsionRecovery : AdicTorsionRecoveryStatement.{u} := by
  intro A _ _ _ _ H G _ hH s
  exact ⟨fun m n hm hn h => s.torsionRestriction_dvd hH hm hn h,
    s.restrict_eq_iff_torsionRestriction hH⟩

end HomScheme.Adic

end Langlands.GroupScheme
