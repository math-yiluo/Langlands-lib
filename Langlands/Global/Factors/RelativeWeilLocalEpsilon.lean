import Langlands.Global.Factors.RelativeWeilBrauer
import Langlands.Global.Factors.RelativeWeilLocalEuler
import Langlands.VirtualRepresentation.Weil.Realization
import Langlands.Weil.Representation.SubquotientContinuity
import Langlands.Correspondence.BaseReciprocityCoherence
import Langlands.LocalFactor.CommonClosureSystemTransport
import Langlands.LocalFactor.CommonClosureInductionTwist
import Langlands.LocalFactor.CommonClosureRankOneEpsilon
import Langlands.Correspondence.RankOneArithmeticEpsilon

/-!
# Arithmetic pair epsilon factors of a local virtual identity

For a p-adic field `F`, a supplied common-closure local-constant system `ε`, and continuous
representations `V`, `W` of `W_F` such that some `T ≃ V ⊗ W` has virtual class
`d [α₀] + Σ_j n_j Ind_{E_j/F}([α_j] - [β_j])`, the arithmetic pair epsilon value at every
admissible bottom-field datum is computed. It is the product of the rank-one abelian
expressions of `α₀` and of the `α_j`, `β_j` over the images of the `E_j` in the common
closure, with the trace characters `ψ ∘ Tr`. This uses additivity, degree-zero induction
and the rank-one relation of the system. The identity's carrier universe is moved to the
system's universe by coordinate models.
-/

noncomputable section

set_option autoImplicit false

universe u w uK uG uH uV uE uA uB uC uA' uB' uC'

namespace Langlands.FiniteRepresentation

variable {G : Type uG} [Group G]

/-- Tensoring with the trivial character line in any carrier universe changes nothing. -/
def tensorCharacterLineOneEquiv (A : FiniteRepresentation.{0, uG, uV} ℂ G) :
    Equiv (tensor A (characterLine.{uG, w} 1)) A where
  toLinearEquiv := (TensorProduct.congr (LinearEquiv.refl ℂ A)
    (ULift.moduleEquiv : ULift.{w} ℂ ≃ₗ[ℂ] ℂ)).trans (TensorProduct.rid ℂ A)
  isIntertwining' g := by
    apply TensorProduct.ext'
    intro x y
    change (((1 : G →* ℂˣ) g : ℂ) * y.down) • A.representation g x =
      A.representation g (y.down • x)
    simp [map_smul]

/-- Restriction of a character line is the character line of the composite character. -/
def restrictCharacterLineEquiv {H : Type uH} [Group H] (φ : H →* G) (χ : G →* ℂˣ) :
    Equiv (restrict φ (characterLine.{uG, w} χ)) (characterLine.{uH, w} (χ.comp φ)) where
  toLinearEquiv := LinearEquiv.refl ℂ _
  isIntertwining' _ := rfl

end Langlands.FiniteRepresentation


namespace Langlands.FiniteRepresentation

section ShortExact

variable {K : Type uK} {G : Type uG} [Field K] [Monoid G]
  {A : FiniteRepresentation.{uK, uG, uA} K G} {B : FiniteRepresentation.{uK, uG, uB} K G}
  {C : FiniteRepresentation.{uK, uG, uC} K G} {A' : FiniteRepresentation.{uK, uG, uA'} K G}
  {B' : FiniteRepresentation.{uK, uG, uB'} K G} {C' : FiniteRepresentation.{uK, uG, uC'} K G}

/-- Short exactness is transported along equivalences of the three terms, with
independent carrier universes. -/
theorem isShortExact_of_equiv {f : A.representation.IntertwiningMap B.representation}
    {g : B.representation.IntertwiningMap C.representation} (h : IsShortExact f g)
    (eA : Equiv A A') (eB : Equiv B B') (eC : Equiv C C') :
    IsShortExact ((eB.toIntertwiningMap.comp f).comp eA.symm.toIntertwiningMap)
      ((eC.toIntertwiningMap.comp g).comp eB.symm.toIntertwiningMap) := by
  refine ⟨?_, ?_, ?_⟩
  · exact (EquivLike.injective eB).comp (h.1.comp (EquivLike.injective eA.symm))
  · exact (EquivLike.surjective eC).comp (h.2.1.comp (EquivLike.surjective eB.symm))
  · ext y
    constructor
    · rintro ⟨x, rfl⟩
      have hx : f (eA.symm x) ∈ LinearMap.ker g.toLinearMap := h.2.2 ▸ ⟨eA.symm x, rfl⟩
      change eC (g (eB.symm (eB (f (eA.symm x))))) = 0
      rw [Representation.Equiv.symm_apply_apply, show g (f (eA.symm x)) = 0 from hx, map_zero]
    · intro hy
      change eC (g (eB.symm y)) = 0 at hy
      have hg : g (eB.symm y) = 0 := (map_eq_zero_iff eC (EquivLike.injective eC)).mp hy
      obtain ⟨x, hx⟩ : eB.symm y ∈ LinearMap.range f.toLinearMap := h.2.2 ▸ hg
      refine ⟨eA x, ?_⟩
      change eB (f (eA.symm (eA x))) = y
      rw [Representation.Equiv.symm_apply_apply]
      change eB (f.toLinearMap x) = y
      rw [hx, Representation.Equiv.apply_symm_apply]

end ShortExact

section UniverseModel

variable {G : Type uG} [Group G]

/-- A coordinate model of a finite-dimensional complex representation, in an arbitrary
carrier universe. -/
def universeModel (A : FiniteRepresentation.{0, uG, uA} ℂ G) :
    FiniteRepresentation.{0, uG, uB} ℂ G :=
  VirtualRepresentation.Weil.liftFiniteRepresentation (FiniteRep.ofRepresentation A.representation)

/-- A representation is equivalent to its coordinate model. -/
def universeModelEquiv (A : FiniteRepresentation.{0, uG, uA} ℂ G) :
    Equiv A (universeModel A : FiniteRepresentation.{0, uG, uB} ℂ G) :=
  (FiniteRep.modelEquiv A.representation).trans
    (VirtualRepresentation.Weil.liftFiniteEquiv _)

end UniverseModel

end Langlands.FiniteRepresentation

namespace Langlands.VirtualRepresentation.ExactGrothendieckGroup

open FiniteRepresentation

section UniverseMap

variable {G : Type uG} [Group G] [TopologicalSpace G]

/-- The class of the coordinate model in another carrier universe. -/
def universeClass :
    IsomorphismClassesWith (fun A : FiniteRepresentation.{0, uG, uA} ℂ G => A.IsContinuous) →
      Continuous.{uG, uB} G :=
  Quotient.lift (fun A => ofRepresentation _ ⟨universeModel A.val,
      (isContinuous_iff_of_equiv (universeModelEquiv A.val)).mp A.property⟩)
    (fun A B h => by
      obtain ⟨e⟩ := h
      exact ofRepresentation_eq_of_equiv _
        (((universeModelEquiv A.val).symm.trans e).trans (universeModelEquiv B.val)))

theorem universeClass_isExactAdditive :
    IsExactAdditive (fun A : FiniteRepresentation.{0, uG, uA} ℂ G => A.IsContinuous)
      (universeClass : _ → Continuous.{uG, uB} G) := by
  intro A B C f g h
  exact ofRepresentation_shortExact _ (isShortExact_of_equiv h (universeModelEquiv A.val)
    (universeModelEquiv B.val) (universeModelEquiv C.val))

/-- Change of carrier universe on continuous exact virtual groups: every class goes to the
class of an equivalent representation in the new carrier universe. -/
def universeMap : Continuous.{uG, uA} G →ₗ[ℤ] Continuous.{uG, uB} G :=
  lift _ universeClass universeClass_isExactAdditive

theorem universeMap_ofRepresentation_of_equiv
    (A : {A : FiniteRepresentation.{0, uG, uA} ℂ G // A.IsContinuous})
    (B : {B : FiniteRepresentation.{0, uG, uB} ℂ G // B.IsContinuous})
    (e : FiniteRepresentation.Equiv A.val B.val) :
    universeMap (ofRepresentation _ A) = ofRepresentation _ B := by
  rw [universeMap, lift_ofRepresentation]
  exact ofRepresentation_eq_of_equiv _ ((universeModelEquiv A.val).symm.trans e)

theorem universeMap_characterClass (χ : G →ₜ* ℂˣ) :
    (universeMap (characterClass.{uG, uA} χ) : Continuous.{uG, uB} G) =
      characterClass.{uG, uB} χ := by
  rw [characterClass, characterClass]
  exact universeMap_ofRepresentation_of_equiv _ _ (characterLineUniverseEquiv χ.toMonoidHom)

variable {H : Type uH} [Group H] [TopologicalSpace H]

theorem universeMap_continuousRestrict (φ : H →ₜ* G) (x : Continuous.{uG, uA} G) :
    (universeMap (ExactGrothendieckGroup.continuousRestrict φ x) : Continuous.{uH, uB} H) =
      ExactGrothendieckGroup.continuousRestrict φ (universeMap x) := by
  have hc : ((universeMap : Continuous.{uH, uA} H →ₗ[ℤ] Continuous.{uH, uB} H).comp
      (ExactGrothendieckGroup.continuousRestrict φ)) =
      (ExactGrothendieckGroup.continuousRestrict φ).comp universeMap := by
    apply hom_ext _
    intro c
    induction c using Quotient.inductionOn with
    | h A =>
      change universeMap (ExactGrothendieckGroup.continuousRestrict φ (ofRepresentation _ A)) =
        ExactGrothendieckGroup.continuousRestrict φ (universeMap (ofRepresentation _ A))
      rw [universeMap_ofRepresentation_of_equiv A ⟨universeModel A.val,
          (isContinuous_iff_of_equiv (universeModelEquiv A.val)).mp A.property⟩
          (universeModelEquiv A.val),
        ExactGrothendieckGroup.continuousRestrict, ExactGrothendieckGroup.restrict_ofRepresentation,
        ExactGrothendieckGroup.continuousRestrict, ExactGrothendieckGroup.restrict_ofRepresentation]
      exact universeMap_ofRepresentation_of_equiv _ _
        (restrictEquivOfEquiv φ.toMonoidHom (universeModelEquiv A.val))
  exact LinearMap.congr_fun hc x

variable [IsTopologicalGroup G]

/-- Induction along an open embedding of a genuine continuous class. -/
theorem continuousInduceAlong_ofRepresentation (φ : H →ₜ* G)
    (hφ : Topology.IsOpenEmbedding φ) [φ.toMonoidHom.range.FiniteIndex]
    (A : {A : FiniteRepresentation.{0, uH, uA} ℂ H // A.IsContinuous}) :
    ExactGrothendieckGroup.continuousInduceAlong φ hφ (ofRepresentation _ A) =
      ofRepresentation _ ⟨induceAlong φ.toMonoidHom hφ.injective A.val,
        isContinuous_induceAlong φ.toMonoidHom hφ A.property⟩ := by
  rw [ExactGrothendieckGroup.continuousInduceAlong, LinearMap.comp_apply,
    ExactGrothendieckGroup.continuousRestrict, ExactGrothendieckGroup.restrict_ofRepresentation,
    ExactGrothendieckGroup.continuousInduce, ExactGrothendieckGroup.induce_ofRepresentation]
  rfl

theorem universeMap_continuousInduceAlong (φ : H →ₜ* G)
    (hφ : Topology.IsOpenEmbedding φ) [φ.toMonoidHom.range.FiniteIndex]
    (x : Continuous.{uH, uA} H) :
    (universeMap (ExactGrothendieckGroup.continuousInduceAlong φ hφ x) :
        Continuous.{uG, max uG uB} G) =
      ExactGrothendieckGroup.continuousInduceAlong φ hφ
        (universeMap x : Continuous.{uH, uB} H) := by
  have hc : ((universeMap : Continuous.{uG, max uG uA} G →ₗ[ℤ] Continuous.{uG, max uG uB} G).comp
      (ExactGrothendieckGroup.continuousInduceAlong φ hφ)) =
      (ExactGrothendieckGroup.continuousInduceAlong φ hφ).comp
        (universeMap : Continuous.{uH, uA} H →ₗ[ℤ] Continuous.{uH, uB} H) := by
    apply hom_ext _
    intro c
    induction c using Quotient.inductionOn with
    | h A =>
      change universeMap (ExactGrothendieckGroup.continuousInduceAlong φ hφ
          (ofRepresentation _ A)) =
        ExactGrothendieckGroup.continuousInduceAlong φ hφ (universeMap (ofRepresentation _ A))
      rw [universeMap_ofRepresentation_of_equiv A ⟨universeModel A.val,
          (isContinuous_iff_of_equiv (universeModelEquiv A.val)).mp A.property⟩
          (universeModelEquiv A.val),
        continuousInduceAlong_ofRepresentation, continuousInduceAlong_ofRepresentation]
      exact universeMap_ofRepresentation_of_equiv _ _
        (induceAlongEquivOfEquiv φ.toMonoidHom hφ.injective (universeModelEquiv A.val))
  exact LinearMap.congr_fun hc x

end UniverseMap


end Langlands.VirtualRepresentation.ExactGrothendieckGroup

namespace Langlands.FiniteRepresentation

section InductionTransport

variable {K : Type uK} [Field K] {G : Type uG} [Group G] {H : Type uH} [Group H]

/-- Restriction along a group isomorphism `φ : H ≃ G` of a representation induced from
`S ≤ G` is the representation induced from a subgroup `S'` of `H` with `φ(S') = S`, by
`f ↦ f ∘ φ`. Here `ψ : S' → S` is `φ` on `S'`. -/
def restrictInduceEquiv (φ : H ≃* G) (S : Subgroup G) [S.FiniteIndex] (S' : Subgroup H)
    [S'.FiniteIndex] (ψ : S' →* S) (hψ : ∀ s, (ψ s : G) = φ s) (hS : ∀ h, φ h ∈ S → h ∈ S')
    (B : FiniteRepresentation.{uK, uG, uA} K S) :
    Equiv (restrict φ.toMonoidHom (induce S B)) (induce S' (restrict ψ B)) where
  toLinearEquiv :=
    { toFun := fun f => ⟨fun h => f.val (φ h), fun s h => by
        change f.val (φ ((s : H) * h)) = B.representation (ψ s) (f.val (φ h))
        rw [map_mul, ← hψ s]
        exact f.property (ψ s) (φ h)⟩
      invFun := fun f => ⟨fun g => f.val (φ.symm g), fun s g => by
        have hs : φ.symm s ∈ S' := hS _ (by simp)
        have hψs : ψ ⟨φ.symm s, hs⟩ = s := Subtype.ext (by rw [hψ]; simp)
        change f.val (φ.symm ((s : G) * g)) = B.representation s (f.val (φ.symm g))
        rw [map_mul]
        conv_rhs => rw [← hψs]
        exact f.property ⟨φ.symm s, hs⟩ (φ.symm g)⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun f => Subtype.ext (funext fun g => by simp)
      right_inv := fun f => Subtype.ext (funext fun h => by simp) }
  isIntertwining' h := by
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    funext x
    change f.val (φ x * φ h) = f.val (φ (x * h))
    rw [map_mul]

end InductionTransport

end Langlands.FiniteRepresentation

namespace Langlands.LocalFactor.CommonClosure

open VirtualRepresentation Weil.Local Correspondence FiniteRepresentation
open LocalClassField

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p)

/-- Every finite intermediate field contains the bottom field. -/
theorem baseExtension_le (L : Extension F) : (baseExtension F).field ≤ L.field := bot_le

/-- Common-closure induction from the image of a standalone extension `E` to the bottom
field is induction along the Weil map `W_E → W_F`, after the standalone transport and
followed by restriction to the bottom-field subgroup. -/
theorem induce_bot_eq_continuousInduceAlong (E : PadicField.{u} p)
    (g : F.Carrier →ₐ[Padic p] E.Carrier)
    (x : Virtual.{u, uV} F (extensionFiniteIntermediate F E g)) :
    induce F (baseExtension F) (extensionFiniteIntermediate F E g) (baseExtension_le F _) x =
      ExactGrothendieckGroup.continuousRestrict
        ((baseWeilEquiv F).symm : weilSubgroup F (baseExtension F) →ₜ* localWeilGroup F)
        (ExactGrothendieckGroup.continuousInduceAlong (extensionWeilMap F E g)
          (extensionWeilMap_isOpenEmbedding F E g)
          (CommonClosureSpectral.Transport.virtualEquiv F E g x)) := by
  let L := extensionFiniteIntermediate F E g
  let ι := (extensionWeilMap F E g).toMonoidHom
  have hι : Function.Injective ι := (extensionWeilMap_isOpenEmbedding F E g).injective
  have hR : ∀ w : localWeilGroup F, w ∈ ι.range ↔ w ∈ weilSubgroup F L :=
    fun w => SetLike.ext_iff.mp (extensionWeilRange_eq_fixing F E g) w
  let S' := (weilSubgroup F L).subgroupOf (weilSubgroup F (baseExtension F))
  let ψ : S' →* ι.range :=
    (((weilSubgroup F (baseExtension F)).subtype).comp S'.subtype).codRestrict ι.range
      (fun s => (hR _).mpr (Subgroup.mem_subgroupOf.mp s.property))
  have hS : ∀ h : weilSubgroup F (baseExtension F),
      (baseWeilEquiv F).symm.toMulEquiv h ∈ ι.range → h ∈ S' :=
    fun h hh => Subgroup.mem_subgroupOf.mpr ((hR _).mp hh)
  have hc : (induce F (baseExtension F) L (baseExtension_le F L) : Virtual.{u, uV} F L →ₗ[ℤ] _) =
      ((ExactGrothendieckGroup.continuousRestrict
        ((baseWeilEquiv F).symm : weilSubgroup F (baseExtension F) →ₜ* localWeilGroup F)).comp
        (ExactGrothendieckGroup.continuousInduceAlong (extensionWeilMap F E g)
          (extensionWeilMap_isOpenEmbedding F E g))).comp
        (CommonClosureSpectral.Transport.virtualEquiv F E g).toLinearMap := by
    apply ExactGrothendieckGroup.hom_ext _
    intro c
    induction c using Quotient.inductionOn with
    | h A =>
      change induce F (baseExtension F) L (baseExtension_le F L)
          (ExactGrothendieckGroup.ofRepresentation _ A) =
        ExactGrothendieckGroup.continuousRestrict
          ((baseWeilEquiv F).symm : weilSubgroup F (baseExtension F) →ₜ* localWeilGroup F)
          (ExactGrothendieckGroup.continuousInduceAlong (extensionWeilMap F E g)
            (extensionWeilMap_isOpenEmbedding F E g)
            (CommonClosureSpectral.Transport.virtualEquiv F E g
              (ExactGrothendieckGroup.ofRepresentation _ A)))
      rw [CommonClosureSpectral.Transport.virtualEquiv_ofRepresentation,
        ExactGrothendieckGroup.continuousInduceAlong_ofRepresentation,
        ExactGrothendieckGroup.continuousRestrict, ExactGrothendieckGroup.restrict_ofRepresentation]
      refine (induce_ofRepresentation F (baseExtension F) L (baseExtension_le F L)
        ⟨A.val, A.property⟩).trans ?_
      apply ExactGrothendieckGroup.ofRepresentation_eq_of_equiv _
      let B₁ := restrict (InductionAlong.rangeInverse ι hι)
        (restrict (extensionImageWeilEquiv F E g).toMonoidHom A.val)
      let e₁ : Equiv (restrict ψ B₁)
          (restrict (nestedWeilEquiv F (baseExtension F) L (baseExtension_le F L) :
            _ →ₜ* _).toMonoidHom A.val) :=
        { toLinearEquiv := LinearEquiv.refl ℂ _
          isIntertwining' := fun s => by
            apply LinearMap.ext
            intro v
            change A.val.representation (extensionImageWeilEquiv F E g
                (InductionAlong.rangeInverse ι hι (ψ s))) v =
              A.val.representation
                (nestedWeilEquiv F (baseExtension F) L (baseExtension_le F L) s) v
            congr 2
            apply Subtype.ext
            change ι (InductionAlong.rangeInverse ι hι (ψ s)) = _
            rw [InductionAlong.apply_rangeInverse]
            rfl }
      exact ((restrictInduceEquiv (baseWeilEquiv F).symm.toMulEquiv ι.range S' ψ
        (fun _ => rfl) hS B₁).trans (induceEquiv S' e₁)).symm
  exact LinearMap.congr_fun hc x

end Langlands.LocalFactor.CommonClosure

namespace Langlands.FiniteRepresentation

section CrossTensor

variable {K : Type uK} [Field K] {G : Type uG} [Group G] {H : Type uH} [Group H]

/-- Tensor product of equivalences with independent carrier universes. -/
def tensorEquivOfEquiv {A : FiniteRepresentation.{uK, uG, uA} K G}
    {A' : FiniteRepresentation.{uK, uG, uA'} K G} {B : FiniteRepresentation.{uK, uG, uB} K G}
    {B' : FiniteRepresentation.{uK, uG, uB'} K G} (e : Equiv A A') (f : Equiv B B') :
    Equiv (tensor A B) (tensor A' B') where
  toLinearEquiv := TensorProduct.congr e.toLinearEquiv f.toLinearEquiv
  isIntertwining' g := by
    apply TensorProduct.ext'
    intro x y
    have hx : e (A.representation g x) = A'.representation g (e x) :=
      Representation.IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap g x
    have hy : f (B.representation g y) = B'.representation g (f y) :=
      Representation.IntertwiningMap.isIntertwining _ _ f.toIntertwiningMap g y
    change e (A.representation g x) ⊗ₜ[K] f (B.representation g y) =
      A'.representation g (e x) ⊗ₜ[K] B'.representation g (f y)
    rw [hx, hy]

/-- Restriction commutes with tensor products; the underlying map is the identity. -/
def restrictTensorIdEquiv (φ : H →* G) (A : FiniteRepresentation.{uK, uG, uA} K G)
    (B : FiniteRepresentation.{uK, uG, uB} K G) :
    Equiv (restrict φ (tensor A B)) (tensor (restrict φ A) (restrict φ B)) where
  toLinearEquiv := LinearEquiv.refl K _
  isIntertwining' _ := rfl

end CrossTensor

end Langlands.FiniteRepresentation

namespace Langlands.Weil.Local.SystemEpsilon

open FiniteRepresentation VirtualRepresentation VirtualRepresentation.ExactGrothendieckGroup
open LocalFactor LocalFactor.CommonClosure LocalFactor.CommonClosureWeilDeligne Correspondence
open LocalClassField

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p)

/-- A continuous character of `W_E` moved to the common-closure subgroup fixing the image
of `E`. -/
def imageCharacter (E : PadicField.{u} p) (g : F.Carrier →ₐ[Padic p] E.Carrier)
    (χ : localWeilGroup E →ₜ* ℂˣ) :
    weilSubgroup F (extensionFiniteIntermediate F E g) →ₜ* ℂˣ :=
  χ.comp ((extensionImageWeilEquiv F E g).symm :
    weilSubgroup F (extensionFiniteIntermediate F E g) →ₜ* localWeilGroup E)

theorem virtualEquiv_symm_characterClass (E : PadicField.{u} p)
    (g : F.Carrier →ₐ[Padic p] E.Carrier) (χ : localWeilGroup E →ₜ* ℂˣ) :
    (CommonClosureSpectral.Transport.virtualEquiv.{u, u, uV} F E g).symm
        (characterClass.{u, max u uV} χ) =
      characterClass.{u, max u uV} (imageCharacter F E g χ) := by
  apply (CommonClosureSpectral.Transport.virtualEquiv.{u, u, uV} F E g).injective
  rw [LinearEquiv.apply_symm_apply]
  change _ = ExactGrothendieckGroup.continuousRestrict _ _
  rw [continuousRestrict_characterClass]
  congr 1
  ext w
  change (χ w : ℂ) = χ ((extensionImageWeilEquiv F E g).symm (extensionImageWeilEquiv F E g w))
  rw [ContinuousMulEquiv.symm_apply_apply]

/-- Restriction to the bottom field of a class induced along `W_E → W_F` is
common-closure induction from the image of `E`. -/
theorem continuousRestrict_continuousInduceAlong (E : PadicField.{u} p)
    (g : F.Carrier →ₐ[Padic p] E.Carrier)
    (y : ExactGrothendieckGroup.Continuous.{u, max u uV} (localWeilGroup E)) :
    ExactGrothendieckGroup.continuousRestrict
        ((baseWeilEquiv F).symm : weilSubgroup F (baseExtension F) →ₜ* localWeilGroup F)
        (ExactGrothendieckGroup.continuousInduceAlong (extensionWeilMap F E g)
          (extensionWeilMap_isOpenEmbedding F E g) y) =
      CommonClosure.induce F (baseExtension F) (extensionFiniteIntermediate F E g)
        (baseExtension_le F _)
        ((CommonClosureSpectral.Transport.virtualEquiv.{u, u, uV} F E g).symm y) := by
  rw [induce_bot_eq_continuousInduceAlong, LinearEquiv.apply_symm_apply]

/-- The spectral twist commutes with common-closure induction. -/
theorem virtualTwist_induce (K L : Extension F) (h : K.field ≤ L.field) (s : ℂ)
    (x : Virtual.{u, uV} F L) :
    CommonClosureSpectral.virtualTwist F K s (CommonClosure.induce F K L h x) =
      CommonClosure.induce F K L h (CommonClosureSpectral.virtualTwist F L s x) := by
  have hc : (CommonClosureSpectral.character F K s).comp (CommonClosure.weilInclusion F K L h) =
      CommonClosureSpectral.character F L s := by
    ext w
    rfl
  change ExactGrothendieckGroup.continuousTwist _ (CommonClosure.induce F K L h x) = _
  rw [CommonClosure.continuousTwist_induce]
  exact congrArg
    (fun χ => CommonClosure.induce F K L h (ExactGrothendieckGroup.continuousTwist χ x)) hc

variable (eC : ReciprocityFamily F) (ε : NonabelianSystem.Assignment.{u, uE} F)
  (hε : NonabelianSystem.IsSystem F eC ε)

/-- The supplied local constant of the spectral twist, as an additive homomorphism. -/
def twistedValueHom (K : Extension F) (ψ : AdditiveCharacter F K) (μ : HaarMeasure F K)
    (s : ℂ) : Virtual.{u, uE} F K →+ Additive ℂˣ where
  toFun x := Additive.ofMul (ε K ψ μ (CommonClosureSpectral.virtualTwist F K s x))
  map_zero' := by
    rw [map_zero, NonabelianSystem.value_zero hε.2.1]
    rfl
  map_add' x y := by
    rw [map_add, hε.2.1]
    rfl

theorem twistedValueHom_characterClass (K : Extension F) (ψ : AdditiveCharacter F K)
    (μ : HaarMeasure F K) (s : ℂ) (χ : weilSubgroup F K →ₜ* ℂˣ) :
    ((Additive.toMul (twistedValueHom F eC ε hε K ψ μ s
      (ExactGrothendieckGroup.characterClass χ)) : ℂˣ) : ℂ) =
      (fieldData F K).abelianEpsilonExpression
        (CommonClosureSpectralAnalytic.fieldCharacterEquiv F eC K
          (CommonClosureSpectral.character F K s * χ)) ψ μ := by
  change (ε K ψ μ (CommonClosureSpectral.virtualTwist F K s
    (ExactGrothendieckGroup.characterClass χ)) : ℂ) = _
  rw [CommonClosureSpectral.virtualTwist_characterClass]
  exact CommonClosureSpectralAnalytic.value_characterClass F eC K ε hε _ ψ μ

/-- Tate (3.4.1) in degree zero: the value at the bottom field of a class induced from the
image of `E` is the value over that image, with the trace character and any Haar measure. -/
theorem twistedValueHom_induce (L : Extension F) (ψ : AdditiveCharacter F (baseExtension F))
    (μ : HaarMeasure F (baseExtension F)) (μL : HaarMeasure F L) (s : ℂ)
    (a b : weilSubgroup F L →ₜ* ℂˣ) :
    ((Additive.toMul (twistedValueHom F eC ε hε (baseExtension F) ψ μ s
        (CommonClosure.induce F (baseExtension F) L (baseExtension_le F L)
          (ExactGrothendieckGroup.characterClass a -
            ExactGrothendieckGroup.characterClass b))) : ℂˣ) : ℂ) =
      (fieldData F L).abelianEpsilonExpression
          (CommonClosureSpectralAnalytic.fieldCharacterEquiv F eC L
            (CommonClosureSpectral.character F L s * a))
          (traceCharacter F (baseExtension F) L (baseExtension_le F L) ψ) μL /
        (fieldData F L).abelianEpsilonExpression
          (CommonClosureSpectralAnalytic.fieldCharacterEquiv F eC L
            (CommonClosureSpectral.character F L s * b))
          (traceCharacter F (baseExtension F) L (baseExtension_le F L) ψ) μL := by
  change (ε (baseExtension F) ψ μ (CommonClosureSpectral.virtualTwist F (baseExtension F) s
    (CommonClosure.induce F (baseExtension F) L (baseExtension_le F L)
          (ExactGrothendieckGroup.characterClass a -
            ExactGrothendieckGroup.characterClass b))) : ℂ) = _
  rw [virtualTwist_induce, map_sub, CommonClosureSpectral.virtualTwist_characterClass,
    CommonClosureSpectral.virtualTwist_characterClass]
  have h0 : ExactGrothendieckGroup.characterClass (CommonClosureSpectral.character F L s * a) -
      ExactGrothendieckGroup.characterClass (CommonClosureSpectral.character F L s * b) ∈
        DegreeZero.{u, uE} F L := by
    rw [ExactGrothendieckGroup.mem_degreeZero, map_sub,
      ExactGrothendieckGroup.degree_characterClass,
      ExactGrothendieckGroup.degree_characterClass, sub_self]
  rw [hε.2.2.2.1 (baseExtension F) L (baseExtension_le F L) ψ μ μL ⟨_, h0⟩]
  change (ε L _ μL
    (ExactGrothendieckGroup.characterClass (CommonClosureSpectral.character F L s * a) -
      ExactGrothendieckGroup.characterClass (CommonClosureSpectral.character F L s * b)) : ℂ) =
    _
  rw [sub_eq_add_neg, hε.2.1, NonabelianSystem.value_neg hε.2.1, Units.val_mul,
    Units.val_inv_eq_inv_val,
    CommonClosureSpectralAnalytic.value_characterClass F eC L ε hε _ _ μL,
    CommonClosureSpectralAnalytic.value_characterClass F eC L ε hε _ _ μL, div_eq_mul_inv]

open WeilDeligneRepresentation in
/-- If a continuous representation `T ≃ V ⊗ W` has virtual class
`d [α₀] + Σ_j n_j Ind_{E_j/F}([α_j] - [β_j])`, then for every admissible bottom-field datum
the arithmetic pair epsilon value of the zero-monodromy pairs of `V` and `W` is
`ε(α₀ ω_s)^d Π_j (ε_{E_j}(α_j ω_s) / ε_{E_j}(β_j ω_s))^{n_j}`, with rank-one constants
given by the abelian expressions of the descended field characters, the trace characters
`ψ ∘ Tr`, and arbitrary Haar measures `μL j` on the images of the `E_j`. -/
theorem conditionalPairEpsilonValue_eq_of_virtualIdentity
    (V W : LocalWeilRepresentation.{u, uA} F) (T : LocalWeilRepresentation.{u, max u w} F)
    (hT : T.IsContinuous) (eT : FiniteRepresentation.Equiv T (FiniteRepresentation.tensor V W))
    {J : Type*} [Fintype J] (E : J → PadicField.{u} p)
    (g : ∀ j, F.Carrier →ₐ[Padic p] (E j).Carrier)
    (α β : ∀ j, localWeilGroup (E j) →ₜ* ℂˣ) (n : J → ℤ)
    (α₀ : localWeilGroup F →ₜ* ℂˣ) (d : ℤ)
    (h : ofRepresentation _ ⟨T, hT⟩ = d • characterClass.{u, max u w} α₀ +
      ∑ j, n j • ExactGrothendieckGroup.continuousInduceAlong (extensionWeilMap F (E j) (g j))
        (extensionWeilMap_isOpenEmbedding F (E j) (g j))
        (characterClass.{u, w} (α j) - characterClass.{u, w} (β j)))
    (ψ : AdditiveCharacter F (baseExtension F)) (μ : HaarMeasure F (baseExtension F))
    (μL : ∀ j, HaarMeasure F (extensionFiniteIntermediate F (E j) (g j)))
    (A B : Pair.{u, uE} F (baseExtension F))
    (hA : IsBaseRestriction F (classOf (zeroMonodromy (localNormCharacter F).toMonoidHom V)) A)
    (hB : IsBaseRestriction F (classOf (zeroMonodromy (localNormCharacter F).toMonoidHom W)) B)
    (hAc : A.toFiniteRepresentation.IsContinuous) (hBc : B.toFiniteRepresentation.IsContinuous)
    (Φ : GeometricFrobenius F (baseExtension F)) (s : ℂ) :
    (CommonClosureGamma.conditionalPairEpsilonValue F eC ε hε (baseExtension F) ψ μ A B hAc hBc
        Φ s : ℂ) =
      (fieldData F (baseExtension F)).abelianEpsilonExpression
          (CommonClosureSpectralAnalytic.fieldCharacterEquiv F eC (baseExtension F)
            (CommonClosureSpectral.character F (baseExtension F) s *
              baseRestrictedWeilCharacter F α₀)) ψ μ ^ d *
        ∏ j, ((fieldData F (extensionFiniteIntermediate F (E j) (g j))).abelianEpsilonExpression
            (CommonClosureSpectralAnalytic.fieldCharacterEquiv F eC _
              (CommonClosureSpectral.character F _ s * imageCharacter F (E j) (g j) (α j)))
            (traceCharacter F (baseExtension F) _ (baseExtension_le F _) ψ) (μL j) /
          (fieldData F (extensionFiniteIntermediate F (E j) (g j))).abelianEpsilonExpression
            (CommonClosureSpectralAnalytic.fieldCharacterEquiv F eC _
              (CommonClosureSpectral.character F _ s * imageCharacter F (E j) (g j) (β j)))
            (traceCharacter F (baseExtension F) _ (baseExtension_le F _) ψ) (μL j)) ^ n j := by
  obtain ⟨fA⟩ := IsBaseRestriction.nonempty_equiv F rfl hA
  obtain ⟨fB⟩ := IsBaseRestriction.nonempty_equiv F rfl hB
  have hNA : A.monodromy = 0 := monodromy_eq_zero_of_equiv fA rfl
  have hNB : B.monodromy = 0 := monodromy_eq_zero_of_equiv fB rfl
  have hN : (WeilDeligneRepresentation.tensor A B).monodromy = 0 := by
    change TensorProduct.map A.monodromy 1 + TensorProduct.map 1 B.monodromy = 0
    rw [hNA, hNB, TensorProduct.map_zero_left, TensorProduct.map_zero_right]
    exact add_zero 0
  let sub : weilSubgroup F (baseExtension F) →ₜ* localWeilGroup F := (baseWeilEquiv F).symm
  have hU : underlyingClass F (baseExtension F) (WeilDeligneRepresentation.tensor A B)
      (CommonClosureGamma.tensor_isContinuous F _ A B hAc hBc) =
      ExactGrothendieckGroup.continuousRestrict sub
        (universeMap (ofRepresentation _ ⟨T, hT⟩)) := by
    rw [← universeMap_continuousRestrict, ExactGrothendieckGroup.continuousRestrict,
      ExactGrothendieckGroup.restrict_ofRepresentation]
    refine (universeMap_ofRepresentation_of_equiv _ _ ?_).symm
    exact ((restrictEquivOfEquiv sub.toMonoidHom eT).trans
      (restrictTensorIdEquiv sub.toMonoidHom V W)).trans
      (tensorEquivOfEquiv fA.representationEquiv fB.representationEquiv)
  have hX : ExactGrothendieckGroup.continuousRestrict sub
      (universeMap (ofRepresentation _ ⟨T, hT⟩) : ExactGrothendieckGroup.Continuous.{u, max u uE}
        (localWeilGroup F)) =
      d • ExactGrothendieckGroup.characterClass (baseRestrictedWeilCharacter F α₀) +
        ∑ j, n j • CommonClosure.induce F (baseExtension F) _ (baseExtension_le F _)
          (ExactGrothendieckGroup.characterClass (imageCharacter F (E j) (g j) (α j)) -
            ExactGrothendieckGroup.characterClass (imageCharacter F (E j) (g j) (β j))) := by
    have hInd : ∀ j (χ : localWeilGroup (E j) →ₜ* ℂˣ),
        (universeMap (ExactGrothendieckGroup.continuousInduceAlong (extensionWeilMap F (E j) (g j))
          (extensionWeilMap_isOpenEmbedding F (E j) (g j)) (characterClass.{u, w} χ)) :
          ExactGrothendieckGroup.Continuous.{u, max u uE} (localWeilGroup F)) =
        ExactGrothendieckGroup.continuousInduceAlong (extensionWeilMap F (E j) (g j))
          (extensionWeilMap_isOpenEmbedding F (E j) (g j)) (characterClass.{u, max u uE} χ) :=
      fun j χ => by
        unfold ExactGrothendieckGroup.characterClass
        rw [continuousInduceAlong_ofRepresentation, continuousInduceAlong_ofRepresentation]
        exact universeMap_ofRepresentation_of_equiv _ _
          (induceAlongEquivOfEquiv _ _ (characterLineUniverseEquiv χ.toMonoidHom))
    have hRes : ∀ j (χ : localWeilGroup (E j) →ₜ* ℂˣ),
        ExactGrothendieckGroup.continuousRestrict sub
          (ExactGrothendieckGroup.continuousInduceAlong (extensionWeilMap F (E j) (g j))
            (extensionWeilMap_isOpenEmbedding F (E j) (g j)) (characterClass.{u, max u uE} χ)) =
        CommonClosure.induce F (baseExtension F) _ (baseExtension_le F _)
          (ExactGrothendieckGroup.characterClass (imageCharacter F (E j) (g j) χ)) :=
      fun j χ => by
        rw [← virtualEquiv_symm_characterClass.{u, uE}]
        exact continuousRestrict_continuousInduceAlong.{u, uE} F (E j) (g j) _
    have h₀ : α₀.comp sub = baseRestrictedWeilCharacter F α₀ := rfl
    rw [h, map_add, map_add, map_zsmul, map_zsmul, universeMap_characterClass,
      continuousRestrict_characterClass, h₀, map_sum, map_sum]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_zsmul, map_zsmul, map_sub, map_sub, hInd, hInd, map_sub, hRes, hRes, map_sub]
  rw [CommonClosureGamma.conditionalPairEpsilonValue,
    conditionalEpsilonValue_of_monodromy_zero F eC ε hε _ ψ μ _ _ hN,
    CommonClosureSpectral.conditionalDeligneValue, hU, hX]
  change ((Additive.toMul (twistedValueHom F eC ε hε (baseExtension F) ψ μ s
    (d • ExactGrothendieckGroup.characterClass (baseRestrictedWeilCharacter F α₀) +
      ∑ j, n j • CommonClosure.induce F (baseExtension F) _ (baseExtension_le F _)
        (ExactGrothendieckGroup.characterClass (imageCharacter F (E j) (g j) (α j)) -
          ExactGrothendieckGroup.characterClass (imageCharacter F (E j) (g j) (β j))))) : ℂˣ) :
    ℂ) = _
  simp only [map_add, map_zsmul, map_sum, toMul_add, toMul_zsmul, toMul_sum, Units.val_mul,
    Units.val_zpow_eq_zpow_val, Units.coe_prod]
  rw [twistedValueHom_characterClass]
  congr 1
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [twistedValueHom_induce F eC ε hε _ ψ μ (μL j)]

end Langlands.Weil.Local.SystemEpsilon
