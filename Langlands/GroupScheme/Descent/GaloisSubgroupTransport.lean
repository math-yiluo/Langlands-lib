import Langlands.GroupScheme.Dynamic.DescentTransport
import Langlands.GroupScheme.Torus.LatticeGalois
import Langlands.GroupScheme.SubgroupBaseChange
import Langlands.GroupScheme.Rational.SplitUnipotentTransport
import Mathlib.FieldTheory.Finite.Basic

/-! # Composition and Frobenius invariance of subgroup descent transport -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.SubgroupFunctor

section Transport

variable {B S : Scheme.{u}} (b : S ⟶ B) (a : S ⟶ S) (ha : a ≫ b = b)
  (G : GroupScheme B)

theorem mem_descentTransport_iff_descentPoint
    (F : SubgroupFunctor ((GroupScheme.baseChange b).obj G))
    {T : Over S} {x : T ⟶ ((GroupScheme.baseChange b).obj G).X} :
    x ∈ (descentTransport b a ha G F).carrier T ↔
      descentPoint b a ha G T x ∈ F.carrier ((Over.map a).obj T) := by
  rw [mem_descentTransport]
  have hx := baseChangePointsEquiv_descent b a ha G T
    (x ≫ (descentBaseChangeIso b a ha G).inv.hom.hom)
  simp only [Category.assoc, ← Grp.comp_hom_hom, Iso.inv_hom_id,
    Grp.id_hom_hom, Category.comp_id] at hx
  have he : baseChangePointsEquiv a ((GroupScheme.baseChange b).obj G) T
      (x ≫ (descentBaseChangeIso b a ha G).inv.hom.hom) =
      descentPoint b a ha G T x := by
    apply (baseChangePointsEquiv b G ((Over.map a).obj T)).injective
    rw [baseChangePointsEquiv_descentPoint, hx, ← Category.assoc,
      Iso.inv_hom_id, Category.id_comp]
  rw [he]

theorem descentTransport_id
    (F : SubgroupFunctor ((GroupScheme.baseChange b).obj G)) :
    descentTransport b (𝟙 S) (Category.id_comp b) G F = F := by
  apply SubgroupFunctor.ext
  intro T
  apply Subgroup.ext
  intro x
  rw [mem_descentTransport_iff_descentPoint, descentPoint_id]
  let e : (Over.map (𝟙 S)).obj T ≅ T := Over.isoMk (Iso.refl _) (by simp)
  change e.hom ≫ x ∈ F.carrier _ ↔ x ∈ F.carrier T
  constructor
  · intro hx
    simpa only [Iso.inv_hom_id_assoc] using F.comp_mem e.inv hx
  · exact F.comp_mem e.hom

theorem descentTransport_comp (c : S ⟶ S) (hc : c ≫ b = b)
    (F : SubgroupFunctor ((GroupScheme.baseChange b).obj G)) :
    descentTransport b a ha G (descentTransport b c hc G F) =
      descentTransport b (a ≫ c) (by rw [Category.assoc, hc, ha]) G F := by
  apply SubgroupFunctor.ext
  intro T
  apply Subgroup.ext
  intro x
  rw [mem_descentTransport_iff_descentPoint, mem_descentTransport_iff_descentPoint,
    mem_descentTransport_iff_descentPoint]
  let e : (Over.map (a ≫ c)).obj T ≅ (Over.map c).obj ((Over.map a).obj T) :=
    Over.isoMk (Iso.refl _) (by simp)
  have he := descentPoint_comp b a ha G c hc T x
  change e.hom ≫ _ = _ at he
  rw [← he]
  constructor
  · exact F.comp_mem e.hom
  · intro hx
    simpa only [Iso.inv_hom_id_assoc] using F.comp_mem e.inv hx

theorem descentTransport_comp_of_eq (c : S ⟶ S) (hc : c ≫ b = b)
    (d : S ⟶ S) (hd : d ≫ b = b) (h : a ≫ c = d)
    (F : SubgroupFunctor ((GroupScheme.baseChange b).obj G)) :
    descentTransport b a ha G (descentTransport b c hc G F) =
      descentTransport b d hd G F := by
  subst d
  exact descentTransport_comp b a ha G c hc F

/-- On a represented subgroup, canonical transport is the range of the
base-changed inclusion followed by the canonical ambient identification. -/
theorem descentTransport_range {H : GroupScheme S}
    (i : H ⟶ (GroupScheme.baseChange b).obj G) :
    descentTransport b a ha G (range i) =
      range ((GroupScheme.baseChange a).map i ≫
        (descentBaseChangeIso b a ha G).hom) := by
  rw [range_comp_iso, range_baseChangeHom]
  rfl

end Transport

section Galois

variable (k L : Type u) [Field k] [Field L] [Algebra k L]
  (G : GroupScheme (Spec (CommRingCat.of k)))

/-- The canonical Galois action on all-test subgroup functors in the pullback
of an actual group over the original field. -/
def galoisTransport : (L ≃ₐ[k] L) →*
    Function.End (SubgroupFunctor ((GroupScheme.baseChange (algebraBaseMap k L)).obj G)) where
  toFun σ := descentTransport (algebraBaseMap k L) (galoisBaseMap k L σ)
    (galoisBaseMap_over k L σ) G
  map_one' := by
    funext F
    change descentTransport (algebraBaseMap k L) (galoisBaseMap k L 1) _ G F = F
    simp only [galoisBaseMap_one]
    exact descentTransport_id _ _ _
  map_mul' σ τ := by
    funext F
    change descentTransport (algebraBaseMap k L) (galoisBaseMap k L (σ * τ)) _ G F =
      descentTransport (algebraBaseMap k L) (galoisBaseMap k L σ) _ G
        (descentTransport (algebraBaseMap k L) (galoisBaseMap k L τ) _ G F)
    exact (descentTransport_comp_of_eq _ _ _ _ _ _ _ _
      (galoisBaseMap_mul k L σ τ).symm F).symm

theorem galoisTransport_pow_eq_self (σ : L ≃ₐ[k] L)
    (F : SubgroupFunctor ((GroupScheme.baseChange (algebraBaseMap k L)).obj G))
    (h : galoisTransport k L G σ F = F) (n : ℕ) :
    galoisTransport k L G (σ ^ n) F = F := by
  induction n with
  | zero => exact congrFun (map_one (galoisTransport k L G)) F
  | succ n ih =>
    rw [pow_succ, map_mul]
    change galoisTransport k L G (σ ^ n) (galoisTransport k L G σ F) = F
    rwa [h]

/-- Over a finite extension of a finite field, an all-test subgroup functor
fixed by the canonical Frobenius transport is fixed by every Galois transport. -/
theorem galoisTransport_eq_self_of_frobenius [Fintype k] [Finite L]
    (F : SubgroupFunctor ((GroupScheme.baseChange (algebraBaseMap k L)).obj G))
    (h : galoisTransport k L G (FiniteField.frobeniusAlgEquivOfAlgebraic k L) F = F)
    (σ : L ≃ₐ[k] L) :
    galoisTransport k L G σ F = F := by
  obtain ⟨n, rfl⟩ := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow k L).2 σ
  exact galoisTransport_pow_eq_self k L G _ F h n.val

/-- Frobenius invariance of a represented all-test range implies the
corresponding equality for every Galois automorphism. -/
theorem galois_range_eq_of_frobenius_range_eq [Fintype k] [Finite L]
    {H : GroupScheme (Spec (CommRingCat.of L))}
    (i : H ⟶ (GroupScheme.baseChange (algebraBaseMap k L)).obj G)
    (h : range
      ((GroupScheme.baseChange (galoisBaseMap k L
        (FiniteField.frobeniusAlgEquivOfAlgebraic k L))).map i ≫
        (descentBaseChangeIso (algebraBaseMap k L) (galoisBaseMap k L
          (FiniteField.frobeniusAlgEquivOfAlgebraic k L))
          (galoisBaseMap_over k L _) G).hom) = range i)
    (σ : L ≃ₐ[k] L) :
    range ((GroupScheme.baseChange (galoisBaseMap k L σ)).map i ≫
      (descentBaseChangeIso (algebraBaseMap k L) (galoisBaseMap k L σ)
        (galoisBaseMap_over k L σ) G).hom) = range i := by
  have hf : galoisTransport k L G (FiniteField.frobeniusAlgEquivOfAlgebraic k L)
      (range i) = range i := by
    change descentTransport _ _ _ _ _ = _
    rw [descentTransport_range]
    exact h
  have hσ := galoisTransport_eq_self_of_frobenius k L G (range i) hf σ
  change descentTransport _ _ _ _ _ = _ at hσ
  rwa [descentTransport_range] at hσ

end Galois

end Langlands.GroupScheme.SubgroupFunctor
