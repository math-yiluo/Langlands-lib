import Langlands.Correspondence.HenniartRankOneStageProof
import Langlands.Weil.Local.GaloisCorrectionProof

/-!
# Finite-order twists of finite-image Weil classes

Two facts used to identify stable images after an unramified twist. A Weil
class factoring through a finite quotient `Q` has a determinant whose values are
`|Q|`-th roots of unity. The twist of such a class by a character of finite order
again factors through a finite quotient of the absolute Galois group: its image
is finite, so it is of Galois type.
-/

noncomputable section

namespace Langlands.Henniart.Extension

open Langlands.Correspondence Langlands.VirtualRepresentation StableMap

universe uG uV uK uW

section Generic

variable {G : Type uG} [Group G]

/-- Finite image transfers along an equivalence of representations. -/
theorem hasFiniteImage_of_equiv {A B : FiniteRepresentation.{0, uG, uV} ℂ G}
    (e : FiniteRepresentation.Equiv A B) (hA : A.HasFiniteImage) : B.HasFiniteImage := by
  apply (hA.image (fun T : Module.End ℂ A => (e.toLinearEquiv.conj T : Module.End ℂ B))).subset
  rintro _ ⟨g, rfl⟩
  refine ⟨A.representation g, ⟨g, rfl⟩, ?_⟩
  ext v
  have h := Representation.IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap g (e.symm v)
  simp only [LinearEquiv.conj_apply, LinearMap.coe_comp, LinearEquiv.coe_coe,
    Function.comp_apply]
  change e (A.representation g (e.symm v)) = B.representation g v
  rw [Representation.Equiv.coe_toIntertwiningMap] at h
  rw [h]
  congr 1
  exact EquivLike.apply_inv_apply e v

/-- The twist of a representation with finite image by a character of finite
order has finite image. -/
theorem hasFiniteImage_twist {A : FiniteRepresentation.{0, uG, uV} ℂ G}
    (hA : A.HasFiniteImage) (χ : G →* ℂˣ) {N : ℕ} (hN : 0 < N) (hχN : ∀ g, χ g ^ N = 1) :
    (FiniteRepresentation.twist χ A).HasFiniteImage := by
  have : NeZero N := ⟨hN.ne'⟩
  have hS : ({ζ : ℂˣ | ζ ^ N = 1} : Set ℂˣ).Finite := by
    have hset : ({ζ : ℂˣ | ζ ^ N = 1} : Set ℂˣ) =
        ((rootsOfUnity N ℂ : Subgroup ℂˣ) : Set ℂˣ) := by
      ext ζ
      simp [mem_rootsOfUnity]
    rw [hset]
    exact Set.finite_coe_iff.mp (inferInstanceAs (Finite (rootsOfUnity N ℂ)))
  apply ((hS.prod hA).image (fun x : ℂˣ × Module.End ℂ A => ((x.1 : ℂ) • x.2))).subset
  rintro _ ⟨g, rfl⟩
  exact ⟨(χ g, A.representation g), ⟨hχN g, ⟨g, rfl⟩⟩, rfl⟩

/-- A class factoring through a finite group `Q` has a determinant with values
in the `|Q|`-th roots of unity. -/
theorem determinant_pow_card_eq_one [TopologicalSpace G] {Q : Type*} [Group Q] [Finite Q]
    (f : G →* Q)
    {b : Weil.IrreducibleBasis.{uG, uV} G} (hb : Weil.FactorsThrough G f b) (g : G) :
    FiniteRepresentation.determinantCharacterClass (Weil.underlyingClass G b) g ^
      Nat.card Q = 1 := by
  obtain ⟨A, hA⟩ := hb
  rw [← hA, ← map_pow]
  change FiniteRepresentation.determinantCharacter
    (FiniteRepresentation.of (A.representation.comp f)) (g ^ Nat.card Q) = 1
  apply Units.ext
  rw [FiniteRepresentation.determinantCharacter_apply]
  change LinearMap.det (A.representation (f (g ^ Nat.card Q))) = 1
  rw [map_pow, pow_card_eq_one', map_one]
  exact map_one LinearMap.det

end Generic

variable {p : ℕ} [Fact p.Prime] (K : PadicField.{uK} p)

local instance henniartFiniteTwistFieldTopology : TopologicalSpace K.Carrier :=
  K.canonicalTopologicalData.topology

/-- The generator of a unitary class in the span of classes factoring through `q`
factors through `q`. -/
theorem factorsThrough_of_mem {Q : Type uK} [Group Q] [Finite Q]
    {q : Field.absoluteGaloisGroup K.Carrier →* Q} {b : LocalWeil.UnitaryBasis.{uK, uW} K}
    (hq : generator b ∈ LocalWeil.unitaryFiniteFactoringSupported.{uK, uW, uK} K q) :
    Weil.FactorsThrough _ (q.comp (Weil.Local.localProjection K).toMonoidHom) b.val := by
  have h := (Finsupp.mem_supported ℤ _).mp hq
  exact h (by simp [generator])

/-- The twist of a finite-image unitary class by a continuous character of finite
order factors through a finite quotient of the absolute Galois group. -/
theorem isFiniteFactoring_twist {b₀ b₁ : LocalWeil.UnitaryBasis.{uK, uW} K}
    (hb₀ : IsFiniteFactoring K b₀) (χ : Weil.Local.localWeilGroup K →ₜ* ℂˣ) {N : ℕ}
    (hN : 0 < N) (hχN : ∀ g, χ g ^ N = 1)
    (hb₁ : b₁.val = Weil.twistBasisEquiv χ b₀.val) : IsFiniteFactoring K b₁ := by
  obtain ⟨Q, _, _, q, hq⟩ := hb₀
  obtain ⟨A, hA⟩ := factorsThrough_of_mem K hq
  obtain ⟨⟨R, hRc, hRi⟩, hR⟩ := Quotient.exists_rep b₀.val.2.val
  have hRclass : Weil.underlyingClass _ b₀.val = FiniteRepresentation.classOf R := by
    change FiniteRepresentation.forgetPropertyClass _ b₀.val.2.val = _
    rw [← hR]
    rfl
  have hAf : (FiniteRepresentation.of
      (A.representation.comp (q.comp (Weil.Local.localProjection K).toMonoidHom))).HasFiniteImage := by
    apply (Set.finite_range A.representation).subset
    rintro _ ⟨g, rfl⟩
    exact ⟨_, rfl⟩
  obtain ⟨e⟩ := (FiniteRepresentation.classOf_eq_iff _ _).mp (hA.trans hRclass)
  have hRf : R.HasFiniteImage := hasFiniteImage_of_equiv e hAf
  let B : Weil.Local.LocalWeilRepresentation.{uK, uW} K :=
    FiniteRepresentation.twist χ.toMonoidHom R
  have hBc : B.IsContinuous := FiniteRepresentation.isContinuous_twist χ hRc
  have hBf : B.HasFiniteImage := hasFiniteImage_twist hRf χ.toMonoidHom hN hχN
  have hG : Weil.Local.IsLocalGaloisType K B :=
    ((Weil.Local.localWeilGaloisTypeFor K B).1).mpr ⟨hBc, hBf⟩
  obtain ⟨Q', _, _, q', ρ, hρ⟩ := LocalWeil.exists_finiteQuotient_of_isLocalGaloisType K B hG
  refine ⟨Q', inferInstance, inferInstance, q', Finsupp.single_mem_supported ℤ _ ?_⟩
  refine ⟨FiniteRepresentation.of ρ, ?_⟩
  change FiniteRepresentation.classOf
      (FiniteRepresentation.of (ρ.comp (q'.comp (Weil.Local.localProjection K).toMonoidHom))) = _
  rw [hρ, hb₁, Weil.underlyingClass_twistBasisEquiv, hRclass,
    FiniteRepresentation.twistClass_classOf]
  rfl

end Langlands.Henniart.Extension
