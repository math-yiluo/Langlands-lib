import Langlands.Representation.Derivative.MirabolicProductRestrictionMackey
import Langlands.Representation.Derivative.MirabolicProductRestrictionStabilizers
import Langlands.Representation.Derivative.MirabolicProductRestrictionFactors
import Langlands.Representation.Derivative.MirabolicProductRestrictionTransport
import Langlands.Representation.Induction.CompactQuotientProof
import Langlands.Representation.Parabolic.QuotientCompactProof
import Langlands.Representation.Twist.SmoothProof
import Langlands.Representation.Smooth.Transfer.PullbackProof

/-!
# Restriction of a binary product to the mirabolic subgroup (BZ77 4.13(a))

The binary normalized product of `A` on `GL_(m+1)` and `B` on `GL_(n+1)`,
restricted to the mirabolic subgroup `P_((m+1)+(n+1))`, contains the right mixed
product `(A|P) × B` with quotient the left mixed product `A × (B|P)`, naturally in
`(A, B)`.
-/

noncomputable section

open CategoryTheory
open scoped TensorProduct

namespace Langlands.Derivative

open GeneralLinear GeneralLinear.Mirabolic.MixedProduct

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}

namespace MirabolicProductRestriction

/-! ### Linear algebra -/

/-- Exactness of a pair of linear maps transported along linear equivalences. -/
theorem exact_of_linearEquiv {M₁ M₂ M₃ N₁ N₂ N₃ : Type*}
    [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
    [AddCommGroup M₃] [Module ℂ M₃] [AddCommGroup N₁] [Module ℂ N₁]
    [AddCommGroup N₂] [Module ℂ N₂] [AddCommGroup N₃] [Module ℂ N₃]
    (e₁ : M₁ ≃ₗ[ℂ] N₁) (e₂ : N₂ ≃ₗ[ℂ] M₂) (e₃ : N₃ ≃ₗ[ℂ] M₃)
    (f : N₁ →ₗ[ℂ] N₂) (g : N₂ →ₗ[ℂ] N₃)
    (hf : Function.Injective f) (hfg : LinearMap.range f = LinearMap.ker g)
    (hg : Function.Surjective g) :
    Function.Injective (e₂.toLinearMap ∘ₗ f ∘ₗ e₁.toLinearMap) ∧
      LinearMap.range (e₂.toLinearMap ∘ₗ f ∘ₗ e₁.toLinearMap) =
        LinearMap.ker (e₃.toLinearMap ∘ₗ g ∘ₗ e₂.symm.toLinearMap) ∧
      Function.Surjective (e₃.toLinearMap ∘ₗ g ∘ₗ e₂.symm.toLinearMap) := by
  refine ⟨e₂.injective.comp (hf.comp e₁.injective), ?_,
    e₃.surjective.comp (hg.comp e₂.symm.surjective)⟩
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    have hy : f (e₁ y) ∈ LinearMap.ker g := hfg ▸ LinearMap.mem_range_self f (e₁ y)
    simp only [LinearMap.mem_ker, LinearMap.coe_comp, LinearEquiv.coe_coe,
      Function.comp_apply, LinearEquiv.symm_apply_apply] at hy ⊢
    rw [hy, map_zero]
  · intro hx
    simp only [LinearMap.mem_ker, LinearMap.coe_comp, LinearEquiv.coe_coe,
      Function.comp_apply, LinearEquiv.map_eq_zero_iff] at hx
    have hx' : e₂.symm x ∈ LinearMap.range f := hfg ▸ hx
    obtain ⟨z, hz⟩ := hx'
    refine ⟨e₁.symm z, ?_⟩
    simp [hz]

/-! ### Equivalence lemmas -/

section EquivLemmas

variable {G : Type*} [Group G] {V W : Type*} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W] {ρ : Representation ℂ G V} {σ : Representation ℂ G W}

/-- An equivalence of representations undoes its inverse. -/
theorem equiv_apply_symm (e : Representation.Equiv ρ σ) (x : W) : e (e.symm x) = x :=
  e.toLinearEquiv.apply_symm_apply x

/-- An equivalence of representations is injective. -/
theorem equiv_injective (e : Representation.Equiv ρ σ) : Function.Injective e :=
  e.toLinearEquiv.injective

end EquivLemmas

variable (T : F.TopologicalData) (m n : ℕ)

/-- The supplied field topology makes `F` a topological ring. -/
theorem topologicalRing : letI := T.topology; IsTopologicalRing F.Carrier := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  infer_instance

/-! ### The inducing data of the binary product -/

/-- Inflation along the binary Levi projection, twisted by `δ^(1/2)`, as a functor
of smooth representations. -/
def leviInducingFunctor :
    letI := T.topology
    SmoothRep.{0, uF, uV} ℂ ((shape m n).Levi F.Carrier) ⥤
      SmoothRep.{0, uF, uV} ℂ (parabolicP F.Carrier m n) :=
  letI := T.topology
  letI := topologicalRing T
  { obj := fun A => SmoothRep.of
      ((shape m n).inducingRepresentation (T.leviHalfCharacter (shape m n)) A.representation)
      ((isSmooth_twist_iff ((shape m n).inflateCharacter (T.leviHalfCharacter (shape m n))).toMonoidHom
        _ ((shape m n).inflateCharacter (T.leviHalfCharacter (shape m n))).isOpen_ker).mpr
        (isSmooth_comp ((shape m n).leviProjection F.Carrier)
          ((shape m n).leviProjectionContinuous F.Carrier).continuous A.isSmooth))
    map := fun f => SmoothRep.ofHom
      ((shape m n).inducingMap (T.leviHalfCharacter (shape m n)) (SmoothRep.hom f))
    map_id := fun _ => by ext; rfl
    map_comp := fun _ _ => by ext; rfl }

/-- The inducing functor `(A, B) ↦ δ^(1/2) (A ⊠ B)` on the binary parabolic. -/
def inducingFunctor :
    letI := T.topology
    (SmoothRep.{0, uF, uV} ℂ (GeneralLinear (m + 1) F.Carrier) ×
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear (n + 1) F.Carrier)) ⥤
      SmoothRep.{0, uF, uV} ℂ (parabolicP F.Carrier m n) :=
  letI := T.topology
  T.binaryPairFamilyFunctor (a := m + 1) (b := n + 1) (Nat.succ_pos m) (Nat.succ_pos n) ⋙
    FiniteTensor.externalFunctor ⋙ leviInducingFunctor T m n

/-- The first term on `P_((m+1)+n+1)`: the right mixed product of `(A|P_(m+1), B)`,
pulled back along the rank identification `P_((m+1)+n+1) ≅ P_((n+1)+m+1)`. -/
abbrev subFunctor :=
  letI := T.topology
  (generalLinearRestriction T m).prod
      (𝟭 (SmoothRep.{0, uF, uV} ℂ (GeneralLinear (n + 1) F.Carrier))) ⋙
    T.rightMixedProductFunctor (n + 1) m ⋙
      MixedProductTensor.pullbackFunctor
        (mirabolicCast (K := F.Carrier) (show (n + 1) + m = (m + 1) + n by omega).symm).toMonoidHom
        (mirabolicCast (K := F.Carrier) (show (n + 1) + m = (m + 1) + n by omega).symm).continuous

/-- The middle term on `P_((m+1)+n+1)`: the binary product restricted to the
mirabolic subgroup. -/
abbrev midFunctor :=
  letI := T.topology
  T.binaryNormalizedProductFunctor.{uF, uV} (m + 1) (n + 1) ⋙
    generalLinearRestriction T ((m + 1) + n)

/-- The last term on `P_((m+1)+n+1)`: the left mixed product of `(A, B|P_(n+1))`. -/
abbrev quotFunctor :=
  letI := T.topology
  (𝟭 (SmoothRep.{0, uF, uV} ℂ (GeneralLinear (m + 1) F.Carrier))).prod
      (generalLinearRestriction T n) ⋙
    T.leftMixedProductFunctor (m + 1) n

/-! ### The middle term -/

/-- The restricted binary product is, by definition, smooth induction of the inducing
data restricted to `Q`. -/
theorem midFunctor_obj_representation
    (X : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear (m + 1) F.Carrier) ×
        SmoothRep.{0, uF, uV} ℂ (GeneralLinear (n + 1) F.Carrier)) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup ((m + 1) + (n + 1))
    ((midFunctor T m n).obj X).representation =
      (Induction.smoothInduced (parabolicP F.Carrier m n)
        ((inducingFunctor T m n).obj X).obj.ρ).comp (mirabolicQ F.Carrier m n).subtype := rfl

/-- Compact induction from `P` restricted to `Q` is the restricted binary product:
the canonical inclusion of compactly supported functions, bijective since
`P \ GL` is compact. -/
def midEquiv
    (X : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear (m + 1) F.Carrier) ×
        SmoothRep.{0, uF, uV} ℂ (GeneralLinear (n + 1) F.Carrier)) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup ((m + 1) + (n + 1))
    Representation.Equiv
      ((Geometric.restrictedCompactInduction.{0, uF, uV} (R := ℂ) (parabolicP F.Carrier m n)
        (mirabolicQ F.Carrier m n)).obj ((inducingFunctor T m n).obj X)).ρ
      ((midFunctor T m n).obj X).representation :=
  letI := T.topology
  letI := T.generalLinearTopologicalGroup ((m + 1) + (n + 1))
  letI : CompactSpace (Induction.LeftQuotient (parabolicP F.Carrier m n)) :=
    Parabolic.parabolicQuotientCompact F T (shape m n)
  BinaryTensor.compEquiv
    ((Induction.compactInclusion (parabolicP F.Carrier m n)
      ((inducingFunctor T m n).obj X).obj.ρ).ofBijective
      (Induction.compactInclusion_bijective_of_compactSpace _ _))
    (mirabolicQ F.Carrier m n).subtype

/-- The identification of the middle term forgets compact support. -/
theorem midEquiv_apply
    (X : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear (m + 1) F.Carrier) ×
        SmoothRep.{0, uF, uV} ℂ (GeneralLinear (n + 1) F.Carrier))
    (f : letI := T.topology
      letI := T.generalLinearTopologicalGroup ((m + 1) + (n + 1))
      (Geometric.restrictedCompactInduction.{0, uF, uV} (R := ℂ) (parabolicP F.Carrier m n)
        (mirabolicQ F.Carrier m n)).obj ((inducingFunctor T m n).obj X)) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup ((m + 1) + (n + 1))
    midEquiv T m n X f = (show Induction.CompactFunctions (parabolicP F.Carrier m n)
      ((inducingFunctor T m n).obj X).obj.ρ from f).val := rfl

/-! ### The tensor factors -/

/-- The two block carriers of `(A, B)`. -/
abbrev factors
    (X : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear (m + 1) F.Carrier) ×
        SmoothRep.{0, uF, uV} ℂ (GeneralLinear (n + 1) F.Carrier)) : Fin 2 → Type uV :=
  letI := T.topology
  fun i => ((T.binaryPairFamilyFunctor (a := m + 1) (b := n + 1) (Nat.succ_pos m) (Nat.succ_pos n)).obj X i : Type uV)

/-- The block tensor of `(A, B)` is `A ⊗ B`. -/
abbrev tensorEquiv
    (X : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear (m + 1) F.Carrier) ×
        SmoothRep.{0, uF, uV} ℂ (GeneralLinear (n + 1) F.Carrier)) :
    PiTensorProduct ℂ (factors T m n X) ≃ₗ[ℂ] (X.1 ⊗[ℂ] X.2) :=
  FiniteTensor.binaryLinearEquiv ℂ (factors T m n X)

/-! ### The closed orbit and the left mixed product -/

/-- The closed-orbit inducing data match the case (II) data through `A ⊗ B`. -/
theorem quot_hE
    (X : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear (m + 1) F.Carrier) ×
        SmoothRep.{0, uF, uV} ℂ (GeneralLinear (n + 1) F.Carrier))
    (s : Geometric.orbitStabilizer (parabolicP F.Carrier m n) (mirabolicQ F.Carrier m n) 1)
    (v : PiTensorProduct ℂ (factors T m n X)) :
    letI := T.topology
    tensorEquiv T m n X ((((inducingFunctor T m n).obj X).obj.ρ.comp
        (Geometric.stabilizerToInducing (parabolicP F.Carrier m n) (mirabolicQ F.Carrier m n) 1))
          s v) =
      (twist (T.leftCharacter (m + 1) n).toMonoidHom
        (leftInducingRepresentation X.1.representation
          ((generalLinearRestriction T n).obj X.2).representation))
        ⟨(ContinuousMulEquiv.refl (mirabolic ((m + 1) + n) F.Carrier)) s.val,
          (mem_closedStabilizer_iff m n s.val).mp s.property⟩ (tensorEquiv T m n X v) := by
  let := T.topology
  obtain ⟨s, hs⟩ := s
  have h0 := closedStabilizer_levi_zero m n s hs
  have h1 := closedStabilizer_levi_one m n s hs
  have hχ := leviHalfModulus_eq_leftLeviCharacter T m n _ _ h1
  change tensorEquiv T m n X ((T.leviHalfModulus (shape m n)
      ((shape m n).leviProjection F.Carrier
        (Geometric.stabilizerToInducing (parabolicP F.Carrier m n) (mirabolicQ F.Carrier m n) 1
          ⟨s, hs⟩)) : ℂ) •
      FiniteTensor.external (fun i => ((T.binaryPairFamilyFunctor (a := m + 1) (b := n + 1) (Nat.succ_pos m)
        (Nat.succ_pos n)).obj X i).representation)
        ((shape m n).leviProjection F.Carrier
          (Geometric.stabilizerToInducing (parabolicP F.Carrier m n) (mirabolicQ F.Carrier m n) 1
            ⟨s, hs⟩)) v) =
    (T.leftLeviCharacter (m + 1) n (leftProjection (⟨s, (mem_closedStabilizer_iff m n s).mp hs⟩ :
        leftSubgroup (m + 1) n F.Carrier)) : ℂ) •
      TensorProduct.map (X.1.representation (leftProjection (⟨s, (mem_closedStabilizer_iff m n s).mp hs⟩ :
        leftSubgroup (m + 1) n F.Carrier)).1)
        (X.2.representation (leftProjection (⟨s, (mem_closedStabilizer_iff m n s).mp hs⟩ :
          leftSubgroup (m + 1) n F.Carrier)).2.val) (tensorEquiv T m n X v)
  have hχ' := hχ.trans (congrArg (fun x => (T.leftLeviCharacter (m + 1) n x : ℂ))
    (Prod.ext h0 rfl))
  have e2 := FiniteTensor.binaryLinearEquiv_external (R := ℂ) (V := factors T m n X)
    (H := fun i : Fin 2 => GeneralLinear ((shape m n).size i) F.Carrier)
    (fun i => ((T.binaryPairFamilyFunctor (a := m + 1) (b := n + 1) (Nat.succ_pos m)
      (Nat.succ_pos n)).obj X i).representation)
    ((shape m n).leviProjection F.Carrier
      (Geometric.stabilizerToInducing (parabolicP F.Carrier m n) (mirabolicQ F.Carrier m n) 1
        ⟨s, hs⟩)) v
  exact (map_smul (tensorEquiv T m n X) _ _).trans (congrArg₂ (· • ·) hχ'
    (e2.trans (congrArg (fun φ : (X.1 ⊗[ℂ] X.2) →ₗ[ℂ] (X.1 ⊗[ℂ] X.2) =>
        φ (tensorEquiv T m n X v))
      (congrArg₂ TensorProduct.map (congrArg (fun x => X.1.representation x) h0)
        (congrArg (fun x => X.2.representation x) h1)))))

/-- The left mixed product `A × (B|P)` is the closed-orbit piece. -/
def quotEquiv
    (X : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear (m + 1) F.Carrier) ×
        SmoothRep.{0, uF, uV} ℂ (GeneralLinear (n + 1) F.Carrier)) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup ((m + 1) + (n + 1))
    Representation.Equiv ((quotFunctor T m n).obj X).representation
      ((Geometric.orbitPiece.{0, uF, uV} (R := ℂ) (parabolicP F.Carrier m n)
        (mirabolicQ F.Carrier m n) 1).obj ((inducingFunctor T m n).obj X)).ρ :=
  letI := T.topology
  letI := T.generalLinearTopologicalGroup ((m + 1) + (n + 1))
  letI := T.generalLinearTopologicalGroup ((m + 1) + n + 1)
  (Representation.Equiv.mk (LinearEquiv.refl ℂ _) (fun _ => rfl)).trans
    (Induction.compactInducedTransport (ContinuousMulEquiv.refl (mirabolic ((m + 1) + n) F.Carrier))
      (Geometric.orbitStabilizer (parabolicP F.Carrier m n) (mirabolicQ F.Carrier m n) 1)
      (leftSubgroup (m + 1) n F.Carrier) (fun s => mem_closedStabilizer_iff m n s) _ _
      (tensorEquiv T m n X) (quot_hE T m n X))

/-! ### The open orbit and the right mixed product -/

/-- The open-orbit inducing data match the case (III) data through `A ⊗ B`. -/
theorem sub_hE
    (X : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear (m + 1) F.Carrier) ×
        SmoothRep.{0, uF, uV} ℂ (GeneralLinear (n + 1) F.Carrier))
    (s : letI := T.topology
      Geometric.orbitStabilizer (parabolicP F.Carrier m n) (mirabolicQ F.Carrier m n)
        (openRep F.Carrier m n))
    (v : PiTensorProduct ℂ (factors T m n X)) :
    letI := T.topology
    tensorEquiv T m n X ((((inducingFunctor T m n).obj X).obj.ρ.comp
        (Geometric.stabilizerToInducing (parabolicP F.Carrier m n) (mirabolicQ F.Carrier m n)
          (openRep F.Carrier m n))) s v) =
      (twist (T.rightCharacter (n + 1) m).toMonoidHom
        (rightInducingRepresentation ((generalLinearRestriction T m).obj X.1).representation
          X.2.representation))
        ⟨openCast (K := F.Carrier) m n s.val, (mem_openStabilizer_iff m n s.val).mp s.property⟩
        (tensorEquiv T m n X v) := by
  let := T.topology
  obtain ⟨s, hs⟩ := s
  have h0 := openStabilizer_levi_zero m n s hs
  have h1 := openStabilizer_levi_one m n s hs
  have hχ := leviHalfModulus_eq_rightLeviCharacter T m n _ _ h0
  change tensorEquiv T m n X ((T.leviHalfModulus (shape m n)
      ((shape m n).leviProjection F.Carrier
        (Geometric.stabilizerToInducing (parabolicP F.Carrier m n) (mirabolicQ F.Carrier m n)
          (openRep F.Carrier m n) ⟨s, hs⟩)) : ℂ) •
      FiniteTensor.external (fun i => ((T.binaryPairFamilyFunctor (a := m + 1) (b := n + 1)
        (Nat.succ_pos m) (Nat.succ_pos n)).obj X i).representation)
        ((shape m n).leviProjection F.Carrier
          (Geometric.stabilizerToInducing (parabolicP F.Carrier m n) (mirabolicQ F.Carrier m n)
            (openRep F.Carrier m n) ⟨s, hs⟩)) v) =
    (T.rightLeviCharacter (n + 1) m (rightProjection (⟨openCast (K := F.Carrier) m n s,
        (mem_openStabilizer_iff m n s).mp hs⟩ : rightSubgroup (n + 1) m F.Carrier)) : ℂ) •
      TensorProduct.map (X.1.representation (rightProjection (⟨openCast (K := F.Carrier) m n s,
          (mem_openStabilizer_iff m n s).mp hs⟩ : rightSubgroup (n + 1) m F.Carrier)).1.val)
        (X.2.representation (rightProjection (⟨openCast (K := F.Carrier) m n s,
          (mem_openStabilizer_iff m n s).mp hs⟩ : rightSubgroup (n + 1) m F.Carrier)).2)
        (tensorEquiv T m n X v)
  let g := (shape m n).leviProjection F.Carrier
    (Geometric.stabilizerToInducing (parabolicP F.Carrier m n) (mirabolicQ F.Carrier m n)
      (openRep F.Carrier m n) ⟨s, hs⟩)
  let rp := rightProjection (⟨openCast (K := F.Carrier) m n s,
    (mem_openStabilizer_iff m n s).mp hs⟩ : rightSubgroup (n + 1) m F.Carrier)
  have hχ' : (T.leviHalfModulus (shape m n) g : ℂ) = (T.rightLeviCharacter (n + 1) m rp : ℂ) :=
    hχ.trans (congrArg (fun x => (T.rightLeviCharacter (n + 1) m x : ℂ))
      (Prod.ext rfl h1 : (rp.1, g (1 : Fin 2)) = rp))
  have e2 := FiniteTensor.binaryLinearEquiv_external (R := ℂ) (V := factors T m n X)
    (H := fun i : Fin 2 => GeneralLinear ((shape m n).size i) F.Carrier)
    (fun i => ((T.binaryPairFamilyFunctor (a := m + 1) (b := n + 1) (Nat.succ_pos m)
      (Nat.succ_pos n)).obj X i).representation)
    ((shape m n).leviProjection F.Carrier
      (Geometric.stabilizerToInducing (parabolicP F.Carrier m n) (mirabolicQ F.Carrier m n)
        (openRep F.Carrier m n) ⟨s, hs⟩)) v
  exact (map_smul (tensorEquiv T m n X) _ _).trans (congrArg₂ (· • ·) hχ'
    (e2.trans (congrArg (fun φ : (X.1 ⊗[ℂ] X.2) →ₗ[ℂ] (X.1 ⊗[ℂ] X.2) =>
        φ (tensorEquiv T m n X v))
      (congrArg₂ TensorProduct.map (congrArg (fun x => X.1.representation x) h0)
        (congrArg (fun x => X.2.representation x) h1)))))

/-- The right mixed product `(A|P) × B`, pulled back to `P_((m+1)+n+1)`, is the
open-orbit piece. -/
def subEquiv
    (X : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear (m + 1) F.Carrier) ×
        SmoothRep.{0, uF, uV} ℂ (GeneralLinear (n + 1) F.Carrier)) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup ((m + 1) + (n + 1))
    Representation.Equiv ((subFunctor T m n).obj X).representation
      ((Geometric.orbitPiece.{0, uF, uV} (R := ℂ) (parabolicP F.Carrier m n)
        (mirabolicQ F.Carrier m n) (openRep F.Carrier m n)).obj
          ((inducingFunctor T m n).obj X)).ρ :=
  letI := T.topology
  letI := T.generalLinearTopologicalGroup ((m + 1) + (n + 1))
  letI := T.generalLinearTopologicalGroup ((m + 1) + n + 1)
  letI := T.generalLinearTopologicalGroup ((n + 1) + m + 1)
  (Representation.Equiv.mk (LinearEquiv.refl ℂ _) (fun _ => rfl)).trans
    (Induction.compactInducedTransport (openCast (K := F.Carrier) m n)
      (Geometric.orbitStabilizer (parabolicP F.Carrier m n) (mirabolicQ F.Carrier m n)
        (openRep F.Carrier m n))
      (rightSubgroup (n + 1) m F.Carrier) (fun s => mem_openStabilizer_iff m n s) _ _
      (tensorEquiv T m n X) (sub_hE T m n X))

/-- The tensor identification commutes with the maps induced by a pair of morphisms. -/
theorem pair_hT
    {X X' : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear (m + 1) F.Carrier) ×
        SmoothRep.{0, uF, uV} ℂ (GeneralLinear (n + 1) F.Carrier)}
    (f : letI := T.topology; X ⟶ X') (w : PiTensorProduct ℂ (factors T m n X)) :
    letI := T.topology
    tensorEquiv T m n X' (FiniteTensor.externalMap (fun i => SmoothRep.hom
      ((T.binaryPairFamilyFunctor (a := m + 1) (b := n + 1) (Nat.succ_pos m)
        (Nat.succ_pos n)).map f i)) w) =
      TensorProduct.map (SmoothRep.hom f.1).toLinearMap (SmoothRep.hom f.2).toLinearMap
        (tensorEquiv T m n X w) :=
  FiniteTensor.binaryLinearEquiv_externalMap _ w

/-! ### Naturality of the identifications -/

/-- Naturality of the open-orbit identification. -/
theorem subEquiv_naturality
    {X X' : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear (m + 1) F.Carrier) ×
        SmoothRep.{0, uF, uV} ℂ (GeneralLinear (n + 1) F.Carrier)}
    (f : letI := T.topology; X ⟶ X')
    (v : letI := T.topology; (subFunctor T m n).obj X) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup ((m + 1) + (n + 1))
    subEquiv T m n X' (SmoothRep.hom ((subFunctor T m n).map f) v) =
      ((Geometric.orbitPiece.{0, uF, uV} (R := ℂ) (parabolicP F.Carrier m n)
        (mirabolicQ F.Carrier m n) (openRep F.Carrier m n)).map
          ((inducingFunctor T m n).map f)).hom (subEquiv T m n X v) := by
  let := T.topology
  let := T.generalLinearTopologicalGroup ((m + 1) + (n + 1))
  let := T.generalLinearTopologicalGroup ((m + 1) + n + 1)
  let := T.generalLinearTopologicalGroup ((n + 1) + m + 1)
  exact Induction.compactInducedTransport_natural (openCast (K := F.Carrier) m n) _ _
    (fun s => mem_openStabilizer_iff m n s) _ _ (tensorEquiv T m n X) (sub_hE T m n X) _ _
    (tensorEquiv T m n X') (sub_hE T m n X')
    ((Rep.resFunctor (Geometric.stabilizerToInducing (parabolicP F.Carrier m n)
      (mirabolicQ F.Carrier m n) (openRep F.Carrier m n))).map
        ((ObjectProperty.ι (fun A : Rep.{uV} ℂ (parabolicP F.Carrier m n) => IsSmooth A.ρ)).map
          ((inducingFunctor T m n).map f))).hom
    (twistIntertwining (T.rightCharacter (n + 1) m).toMonoidHom
      (MixedProductTensor.pullbackMap rightProjection
        (MixedProductTensor.externalMap (SmoothRep.hom ((generalLinearRestriction T m).map f.1))
          (SmoothRep.hom f.2))))
    (pair_hT T m n f) v

/-- Naturality of the closed-orbit identification. -/
theorem quotEquiv_naturality
    {X X' : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear (m + 1) F.Carrier) ×
        SmoothRep.{0, uF, uV} ℂ (GeneralLinear (n + 1) F.Carrier)}
    (f : letI := T.topology; X ⟶ X')
    (v : letI := T.topology; (quotFunctor T m n).obj X) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup ((m + 1) + (n + 1))
    quotEquiv T m n X' (SmoothRep.hom ((quotFunctor T m n).map f) v) =
      ((Geometric.orbitPiece.{0, uF, uV} (R := ℂ) (parabolicP F.Carrier m n)
        (mirabolicQ F.Carrier m n) 1).map
          ((inducingFunctor T m n).map f)).hom (quotEquiv T m n X v) := by
  let := T.topology
  let := T.generalLinearTopologicalGroup ((m + 1) + (n + 1))
  let := T.generalLinearTopologicalGroup ((m + 1) + n + 1)
  exact Induction.compactInducedTransport_natural
    (ContinuousMulEquiv.refl (mirabolic ((m + 1) + n) F.Carrier)) _ _
    (fun s => mem_closedStabilizer_iff m n s) _ _ (tensorEquiv T m n X) (quot_hE T m n X) _ _
    (tensorEquiv T m n X') (quot_hE T m n X')
    ((Rep.resFunctor (Geometric.stabilizerToInducing (parabolicP F.Carrier m n)
      (mirabolicQ F.Carrier m n) 1)).map
        ((ObjectProperty.ι (fun A : Rep.{uV} ℂ (parabolicP F.Carrier m n) => IsSmooth A.ρ)).map
          ((inducingFunctor T m n).map f))).hom
    (twistIntertwining (T.leftCharacter (m + 1) n).toMonoidHom
      (MixedProductTensor.pullbackMap leftProjection
        (MixedProductTensor.externalMap (SmoothRep.hom f.1)
          (SmoothRep.hom ((generalLinearRestriction T n).map f.2)))))
    (pair_hT T m n f) v

/-- Naturality of the middle identification. -/
theorem midEquiv_naturality
    {X X' : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear (m + 1) F.Carrier) ×
        SmoothRep.{0, uF, uV} ℂ (GeneralLinear (n + 1) F.Carrier)}
    (f : letI := T.topology; X ⟶ X')
    (u : letI := T.topology
      letI := T.generalLinearTopologicalGroup ((m + 1) + (n + 1))
      (Geometric.restrictedCompactInduction.{0, uF, uV} (R := ℂ) (parabolicP F.Carrier m n)
        (mirabolicQ F.Carrier m n)).obj ((inducingFunctor T m n).obj X)) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup ((m + 1) + (n + 1))
    midEquiv T m n X' (((Geometric.restrictedCompactInduction.{0, uF, uV} (R := ℂ)
      (parabolicP F.Carrier m n) (mirabolicQ F.Carrier m n)).map
        ((inducingFunctor T m n).map f)).hom u) =
      SmoothRep.hom ((midFunctor T m n).map f) (midEquiv T m n X u) := rfl

/-! ### The sequence on `P_((m+1)+n+1)` -/

/-- The natural short exact sequence on `P_((m+1)+n+1)`, before the final rank cast. -/
theorem core :
    letI := T.topology
    ∃ (i : subFunctor.{uF, uV} T m n ⟶ midFunctor T m n)
      (q : midFunctor.{uF, uV} T m n ⟶ quotFunctor T m n),
      ∀ X, ExactAt (i.app X) (q.app X) := by
  let := T.topology
  let := T.generalLinearTopologicalGroup ((m + 1) + (n + 1))
  obtain ⟨ic, qc, hc⟩ := exists_exact_restrictedCompactInduction.{uF, uV} T m n
  refine ⟨⟨fun X => SmoothRep.ofHom ((midEquiv T m n X).toIntertwiningMap.comp
        ((ic.app ((inducingFunctor T m n).obj X)).hom.comp (subEquiv T m n X).toIntertwiningMap)),
      ?_⟩,
    ⟨fun X => SmoothRep.ofHom ((quotEquiv T m n X).symm.toIntertwiningMap.comp
        ((qc.app ((inducingFunctor T m n).obj X)).hom.comp
          (midEquiv T m n X).symm.toIntertwiningMap)),
      ?_⟩, fun X => ?_⟩
  · intro X X' f
    apply MixedProductTensor.smoothRep_hom_ext
    intro v
    change midEquiv T m n X' ((ic.app ((inducingFunctor T m n).obj X')).hom
        (subEquiv T m n X' (SmoothRep.hom ((subFunctor T m n).map f) v))) =
      SmoothRep.hom ((midFunctor T m n).map f) (midEquiv T m n X
        ((ic.app ((inducingFunctor T m n).obj X)).hom (subEquiv T m n X v)))
    rw [subEquiv_naturality]
    have hn := congrArg (fun φ => φ.hom (subEquiv T m n X v))
      (ic.naturality ((inducingFunctor T m n).map f))
    exact (congrArg (midEquiv T m n X') hn).trans (midEquiv_naturality T m n f _)
  · intro X X' f
    apply MixedProductTensor.smoothRep_hom_ext
    intro u
    change (quotEquiv T m n X').symm ((qc.app ((inducingFunctor T m n).obj X')).hom
        ((midEquiv T m n X').symm (SmoothRep.hom ((midFunctor T m n).map f) u))) =
      SmoothRep.hom ((quotFunctor T m n).map f) ((quotEquiv T m n X).symm
        ((qc.app ((inducingFunctor T m n).obj X)).hom ((midEquiv T m n X).symm u)))
    have h1 : (midEquiv T m n X').symm (SmoothRep.hom ((midFunctor T m n).map f) u) =
        ((Geometric.restrictedCompactInduction.{0, uF, uV} (R := ℂ) (parabolicP F.Carrier m n)
          (mirabolicQ F.Carrier m n)).map ((inducingFunctor T m n).map f)).hom
            ((midEquiv T m n X).symm u) := by
      apply equiv_injective (midEquiv T m n X')
      rw [equiv_apply_symm, midEquiv_naturality, equiv_apply_symm]
    have hn := congrArg (fun φ => φ.hom ((midEquiv T m n X).symm u))
      (qc.naturality ((inducingFunctor T m n).map f))
    have h3 : ∀ z, (quotEquiv T m n X').symm (((Geometric.orbitPiece.{0, uF, uV} (R := ℂ)
        (parabolicP F.Carrier m n) (mirabolicQ F.Carrier m n) 1).map
          ((inducingFunctor T m n).map f)).hom z) =
        SmoothRep.hom ((quotFunctor T m n).map f) ((quotEquiv T m n X).symm z) := by
      intro z
      apply equiv_injective (quotEquiv T m n X')
      rw [equiv_apply_symm, quotEquiv_naturality, equiv_apply_symm]
    rw [h1]
    exact (congrArg (quotEquiv T m n X').symm hn).trans (h3 _)
  · exact exact_of_linearEquiv (subEquiv T m n X).toLinearEquiv
      (midEquiv T m n X).toLinearEquiv (quotEquiv T m n X).symm.toLinearEquiv
      (ic.app ((inducingFunctor T m n).obj X)).hom.toLinearMap
      (qc.app ((inducingFunctor T m n).obj X)).hom.toLinearMap
      (hc _).1 (hc _).2.1 (hc _).2.2

end MirabolicProductRestriction

open MirabolicProductRestriction in
/-- BZ77 Proposition 4.13(a): for all positive ranks, the restriction of the binary
product to the mirabolic subgroup is a natural extension of the left mixed product
`A × (B|P)` by the right mixed product `(A|P) × B`. -/
theorem mirabolicProductRestriction {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
    (T : F.TopologicalData) : MirabolicProductRestrictionStatement.{uF, uV} F T := by
  intro m n
  rw [restrictedProduct_eq, restrictionSubobject_eq, restrictionQuotient_eq]
  exact exists_exact_comp_mirabolicRankCast T (show (m + 1) + n = m + n + 1 by omega)
    (core T m n)

end Langlands.Derivative
