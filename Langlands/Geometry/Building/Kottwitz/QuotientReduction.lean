import Langlands.Geometry.Building.Kottwitz.QuotientStatement
import Langlands.Geometry.Building.Kottwitz.ZeroKernelStatement
import Langlands.Geometry.Building.Kottwitz.CharacterKernelStatement
import Langlands.Geometry.Building.Kottwitz.ChamberStatement

/-! # KP Corollary 11.7.6 from Lemma 11.5.2, Proposition 11.5.4 and rational surjectivity -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme

namespace Langlands.Geometry.Building.Kottwitz

/-- The three quotients induced by a surjective homomorphism `κ : Γ → A` to a
commutative group, when `N` is its kernel and `H` is the inverse image of a
subgroup `T`. -/
theorem quotients_of_surjective_of_ker_of_comap {Γ : Type*} {A : Type*}
    [Group Γ] [CommGroup A] (κ : Γ →* A) (hκ : Function.Surjective κ)
    (N H : Subgroup Γ) [H.Normal] (T : Subgroup A)
    (hN : N = κ.ker) (hH : H = T.comap κ) :
    ∃ hN : N.Normal,
      letI := hN
      N ≤ H ∧
      (∃ e : (Γ ⧸ N) ≃* A, ∀ g, e (QuotientGroup.mk' N g) = κ g) ∧
      (∃ e : (H ⧸ N.subgroupOf H) ≃* T,
        ∀ x : H, (e (QuotientGroup.mk' (N.subgroupOf H) x) : A) = κ x.val) ∧
      (∃ e : (Γ ⧸ H) ≃* (A ⧸ T),
        ∀ g, e (QuotientGroup.mk' H g) = QuotientGroup.mk' T (κ g)) := by
  subst hN hH
  refine ⟨inferInstance, ?_, ?_, ?_, ?_⟩
  · intro g hg
    rw [MonoidHom.mem_ker] at hg
    rw [Subgroup.mem_comap, hg]
    exact T.one_mem
  · exact ⟨QuotientGroup.quotientKerEquivOfSurjective κ hκ, fun _ => rfl⟩
  · let κH : T.comap κ →* T :=
      (κ.comp (T.comap κ).subtype).codRestrict T (fun x => x.property)
    have hsurj : Function.Surjective κH := by
      intro t
      obtain ⟨g, hg⟩ := hκ t
      refine ⟨⟨g, ?_⟩, Subtype.ext hg⟩
      rw [Subgroup.mem_comap, hg]
      exact t.property
    have hker : κ.ker.subgroupOf (T.comap κ) = κH.ker := by
      ext x
      rw [Subgroup.mem_subgroupOf, MonoidHom.mem_ker, MonoidHom.mem_ker]
      constructor
      · intro h
        exact Subtype.ext h
      · intro h
        exact congrArg Subtype.val h
    exact ⟨(QuotientGroup.quotientMulEquivOfEq hker).trans
      (QuotientGroup.quotientKerEquivOfSurjective κH hsurj), fun _ => rfl⟩
  · let q : Γ →* A ⧸ T := (QuotientGroup.mk' T).comp κ
    have hsurj : Function.Surjective q :=
      (QuotientGroup.mk'_surjective T).comp hκ
    have hker : T.comap κ = q.ker := by
      ext g
      rw [Subgroup.mem_comap, MonoidHom.mem_ker, MonoidHom.comp_apply,
        QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact ⟨(QuotientGroup.quotientMulEquivOfEq hker).trans
      (QuotientGroup.quotientKerEquivOfSurjective q hsurj), fun _ => rfl⟩

/-- Lemma 11.5.2, Proposition 11.5.4 and surjectivity of the rational Kottwitz
map imply Corollary 11.7.6. -/
def QuotientReductionStatement : Prop :=
  ZeroKernelStatement.{u} → CharacterKernelStatement.{u} →
  (∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G),
    Function.Surjective (reductiveKottwitzRational F G hG)) →
  QuotientStatement.{u}

/-- The reduction of Corollary 11.7.6 to its three inputs. -/
theorem quotientReduction : QuotientReductionStatement.{u} := by
  intro hzero hchar hsurj F _ _ _ _ G hG S Z i j d
  exact quotients_of_surjective_of_ker_of_comap (reductiveKottwitzRational F G hG)
    (hsurj F G hG) _ _ _ (hzero F G hG S Z i j d) (hchar F G hG)

/-- Corollary 11.7.6 from Lemma 11.5.2, Proposition 11.5.4 and the
surjectivity clause of Corollary 11.7.5. -/
theorem quotientStatement_of_chamberStatement
    (hzero : ZeroKernelStatement.{u}) (hchar : CharacterKernelStatement.{u})
    (hchamber : ChamberStatement.{u}) : QuotientStatement.{u} :=
  quotientReduction hzero hchar (fun F _ _ _ _ G hG => (hchamber F G hG).1)

end Langlands.Geometry.Building.Kottwitz
