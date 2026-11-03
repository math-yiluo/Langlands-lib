import Langlands.Representation.Induction.FiniteProductTensorBijectiveProof
import Langlands.Representation.Induction.SmoothGroupTransport
import Langlands.Representation.Induction.Equivalences
import Mathlib.Algebra.Module.ULift

noncomputable section

open scoped TensorProduct

namespace Langlands.Induction.BinaryTensor

universe uR uG uH uV uW uX uY

section General

variable {R : Type uR} [CommRing R] {G : Type uG} {H : Type uH} [Group G] [Group H]
variable {V : Type uV} {W : Type uW}
variable [AddCommGroup V] [AddCommGroup W] [Module R V] [Module R W]

/-- External product on ordinary binary groups, with independent universes. -/
def external (σ : Representation R G V) (τ : Representation R H W) :
    Representation R (G × H) (V ⊗[R] W) :=
  Representation.tprod (σ.comp (MonoidHom.fst G H)) (τ.comp (MonoidHom.snd G H))

@[simp] theorem external_tmul (σ : Representation R G V) (τ : Representation R H W)
    (g : G × H) (v : V) (w : W) :
    external σ τ g (v ⊗ₜ[R] w) = σ g.1 v ⊗ₜ[R] τ g.2 w := rfl

/-- The actual inducing representation on the product subgroup. -/
def inducing (P : Subgroup G) (Q : Subgroup H)
    (σ : Representation R P V) (τ : Representation R Q W) :
    Representation R (P.prod Q) (V ⊗[R] W) :=
  (external σ τ).comp (P.prodEquiv Q).toMonoidHom

/-- Pull an equivalence back along a group homomorphism. -/
def pullEquiv {ρ : Representation R G V} {τ : Representation R G W}
    (e : ρ.Equiv τ) (φ : H →* G) : Representation.Equiv (ρ.comp φ) (τ.comp φ) :=
  Representation.Equiv.mk (ρ := ρ.comp φ) (σ := τ.comp φ)
    e.toLinearEquiv (fun h => e.isIntertwining' (φ h))

end General

abbrev Index := Unit ⊕ Unit

abbrev family (V W : Type uV) : Index → Type uV
  | .inl _ => V
  | .inr _ => W

def tuple {V W : Type uV} (v : V) (w : W) : ∀ i, family V W i
  | .inl _ => v
  | .inr _ => w

instance familyAddCommGroup (V W : Type uV) [AddCommGroup V] [AddCommGroup W] :
    ∀ i, AddCommGroup (family V W i) := by
  intro i
  cases i <;> exact inferInstance

instance familyModule (R : Type uR) [CommRing R] (V W : Type uV)
    [AddCommGroup V] [AddCommGroup W] [Module R V] [Module R W] :
    ∀ i, Module R (family V W i) := by
  intro i
  cases i <;> exact inferInstance

variable (R : Type uR) [CommRing R] (V W : Type uV)
variable [AddCommGroup V] [AddCommGroup W] [Module R V] [Module R W]

/-- The ordinary binary tensor as an indexed tensor on two singleton blocks. -/
def tensorEquiv : V ⊗[R] W ≃ₗ[R] PiTensorProduct R (family V W) :=
  (TensorProduct.congr
    (PiTensorProduct.subsingletonEquiv (R := R) (s := fun _ : Unit => V) ()).symm
    (PiTensorProduct.subsingletonEquiv (R := R) (s := fun _ : Unit => W) ()).symm).trans
    (PiTensorProduct.tmulEquivDep R (family V W))

@[simp] theorem tensorEquiv_tmul (v : V) (w : W) :
    tensorEquiv R V W (v ⊗ₜ[R] w) =
      PiTensorProduct.tprod R (tuple v w) := by
  simp [tensorEquiv]
  congr 1
  funext i
  cases i <;> rfl

/-- Binary regrouping for an arbitrary dependent two-block family. -/
def tensorEquivDep (N : Index → Type uV) [∀ i, AddCommGroup (N i)] [∀ i, Module R (N i)] :
    N (.inl ()) ⊗[R] N (.inr ()) ≃ₗ[R] PiTensorProduct R N :=
  (TensorProduct.congr
    (PiTensorProduct.subsingletonEquiv (R := R) (s := fun i : Unit => N (.inl i)) ()).symm
    (PiTensorProduct.subsingletonEquiv (R := R) (s := fun i : Unit => N (.inr i)) ()).symm).trans
    (PiTensorProduct.tmulEquivDep R N)

@[simp] theorem tensorEquivDep_symm_tprod (N : Index → Type uV)
    [∀ i, AddCommGroup (N i)] [∀ i, Module R (N i)] (f : ∀ i, N i) :
    (tensorEquivDep R N).symm (PiTensorProduct.tprod R f) =
      f (.inl ()) ⊗ₜ[R] f (.inr ()) := by
  simp [tensorEquivDep]

theorem tensorEquivDep_tprod (N : Index → Type uV)
    [∀ i, AddCommGroup (N i)] [∀ i, Module R (N i)] (f : ∀ i, N i) :
    tensorEquivDep R N (f (.inl ()) ⊗ₜ[R] f (.inr ())) = PiTensorProduct.tprod R f := by
  apply (tensorEquivDep R N).symm.injective
  simp

variable {R V W}
variable (G H : Type uG) [Group G] [Group H]

instance familyGroup : ∀ i, Group (family G H i) := by
  intro i
  cases i <;> exact inferInstance

instance familyTopology [TopologicalSpace G] [TopologicalSpace H] :
    ∀ i, TopologicalSpace (family G H i) := by
  intro i
  cases i <;> exact inferInstance

instance familyTopologicalGroup [TopologicalSpace G] [TopologicalSpace H]
    [IsTopologicalGroup G] [IsTopologicalGroup H] :
    ∀ i, IsTopologicalGroup (family G H i) := by
  intro i
  cases i <;> exact inferInstance

/-- Binary tuples and two-singleton indexed tuples, with their actual topologies. -/
def groupEquiv [TopologicalSpace G] [TopologicalSpace H] :
    G × H ≃ₜ* (∀ i, family G H i) where
  toFun x := tuple x.1 x.2
  invFun f := (f (.inl ()), f (.inr ()))
  left_inv _ := rfl
  right_inv f := by funext i; rcases i with (i | i) <;> cases i <;> rfl
  map_mul' _ _ := by funext i; rcases i with (i | i) <;> cases i <;> rfl
  continuous_toFun := continuous_pi (by intro i; cases i <;> simpa only [tuple] using (by fun_prop))
  continuous_invFun := (continuous_apply (Sum.inl () : Index)).prodMk (continuous_apply (Sum.inr () : Index))

variable {G H}
variable (P : Subgroup G) (Q : Subgroup H)

abbrev subgroupFamily : ∀ i, Subgroup (family G H i)
  | .inl _ => P
  | .inr _ => Q

/-- The product subgroup is literally the indexed coordinatewise subgroup. -/
def subgroupEquiv [TopologicalSpace G] [TopologicalSpace H] :
    P.prod Q ≃* Subgroup.pi Set.univ (subgroupFamily P Q) where
  toFun p := ⟨groupEquiv G H p.1, by intro i _; cases i <;> first | exact p.2.1 | exact p.2.2⟩
  invFun p := ⟨((groupEquiv G H).symm p.1), ⟨p.2 (.inl ()) (Set.mem_univ _),
    p.2 (.inr ()) (Set.mem_univ _)⟩⟩
  left_inv p := Subtype.ext rfl
  right_inv p := by apply Subtype.ext; funext i; rcases i with (i | i) <;> cases i <;> rfl
  map_mul' p q := by apply Subtype.ext; funext i; rcases i with (i | i) <;> cases i <;> rfl

variable (σ : Representation R P V) (τ : Representation R Q W)

def representationFamily : ∀ i, Representation R (subgroupFamily P Q i) (family V W i)
  | .inl _ => σ
  | .inr _ => τ

instance familyNonarchimedean [TopologicalSpace G] [TopologicalSpace H]
    [NonarchimedeanGroup G] [NonarchimedeanGroup H] :
    ∀ i, NonarchimedeanGroup (family G H i) := by
  intro i
  cases i <;> exact inferInstance

instance familyWeaklyLocallyCompact [TopologicalSpace G] [TopologicalSpace H]
    [WeaklyLocallyCompactSpace G] [WeaklyLocallyCompactSpace H] :
    ∀ i, WeaklyLocallyCompactSpace (family G H i) := by
  intro i
  cases i <;> exact inferInstance

instance familyCompactQuotient [TopologicalSpace G] [TopologicalSpace H]
    [CompactSpace (LeftQuotient P)] [CompactSpace (LeftQuotient Q)] :
    ∀ i, CompactSpace (LeftQuotient (subgroupFamily P Q i)) := by
  intro i
  cases i <;> exact inferInstance

variable [TopologicalSpace G] [TopologicalSpace H]

/-- Tensor transport for the inducing action on the actual product subgroup. -/
def inducingEquiv [IsTopologicalGroup G] [IsTopologicalGroup H] :
    (inducing P Q σ τ).Equiv
      ((productInducing (subgroupFamily P Q) (representationFamily P Q σ τ)).comp
        (subgroupEquiv P Q).toMonoidHom) where
  toLinearEquiv := tensorEquiv R V W
  isIntertwining' p := by
    ext v w
    change tensorEquiv R V W (σ ⟨p.1.1, p.2.1⟩ v ⊗ₜ[R] τ ⟨p.1.2, p.2.2⟩ w) = _
    rw [tensorEquiv_tmul]
    change _ = productInducing (subgroupFamily P Q) (representationFamily P Q σ τ)
      (subgroupEquiv P Q p) (tensorEquiv R V W (v ⊗ₜ[R] w))
    rw [tensorEquiv_tmul, productInducing_tprod]
    congr 1
    funext i
    cases i <;> rfl

/-- Binary external induced action as the two-index external induced action. -/
def inducedTensorEquiv [IsTopologicalGroup G] [IsTopologicalGroup H] :
    (external (smoothInduced P σ) (smoothInduced Q τ)).Equiv
      ((FiniteTensor.external (fun i => smoothInduced (subgroupFamily P Q i)
        (representationFamily P Q σ τ i))).comp (groupEquiv G H).toMonoidHom) where
  toLinearEquiv := tensorEquivDep R (fun i => SmoothFunctions (subgroupFamily P Q i)
    (representationFamily P Q σ τ i))
  isIntertwining' g := by
    ext f h
    let N := fun i => SmoothFunctions (subgroupFamily P Q i) (representationFamily P Q σ τ i)
    let F : ∀ i, N i := fun | .inl _ => f | .inr _ => h
    change tensorEquivDep R N (smoothInduced P σ g.1 f ⊗ₜ[R] smoothInduced Q τ g.2 h) =
      FiniteTensor.external (fun i => smoothInduced (subgroupFamily P Q i)
        (representationFamily P Q σ τ i)) (groupEquiv G H g)
          (tensorEquivDep R N (f ⊗ₜ[R] h))
    rw [show tensorEquivDep R N (f ⊗ₜ[R] h) = PiTensorProduct.tprod R F from
      tensorEquivDep_tprod R N F, FiniteTensor.external_tprod]
    exact tensorEquivDep_tprod R N (fun i => smoothInduced (subgroupFamily P Q i)
      (representationFamily P Q σ τ i) (groupEquiv G H g i) (F i))

/-- Transport indexed product induction back to the ordinary binary product. -/
def productInducedEquiv [IsTopologicalGroup G] [IsTopologicalGroup H] :
    Representation.Equiv ((smoothInduced (Subgroup.pi Set.univ (subgroupFamily P Q))
      (productInducing (subgroupFamily P Q) (representationFamily P Q σ τ))).comp
        (groupEquiv G H).toMonoidHom) (smoothInduced (P.prod Q) (inducing P Q σ τ)) :=
  (precomposeSmoothInducedGroupEquiv
    (σ := productInducing (subgroupFamily P Q) (representationFamily P Q σ τ))
    (groupEquiv G H) (subgroupEquiv P Q)
    (fun _ => rfl) (fun _ => rfl)).trans
      (smoothInducedEquiv (P.prod Q) (inducingEquiv P Q σ τ).symm)

section Field

variable {k : Type uR} [Field k]
variable {V W : Type uV} [AddCommGroup V] [AddCommGroup W] [Module k V] [Module k W]
variable (σ : Representation k P V) (τ : Representation k Q W)
variable [NonarchimedeanGroup G] [NonarchimedeanGroup H]
variable [WeaklyLocallyCompactSpace G] [WeaklyLocallyCompactSpace H]
variable [CompactSpace (LeftQuotient P)] [CompactSpace (LeftQuotient Q)]

/-- The published finite-product map, pulled back to the binary product group. -/
def finiteEquiv :
    Representation.Equiv ((FiniteTensor.external (fun i => smoothInduced (subgroupFamily P Q i)
      (representationFamily P Q σ τ i))).comp (groupEquiv G H).toMonoidHom)
    ((smoothInduced (Subgroup.pi Set.univ (subgroupFamily P Q))
      (productInducing (subgroupFamily P Q) (representationFamily P Q σ τ))).comp
        (groupEquiv G H).toMonoidHom) := by
  let e := (finiteProductTensorMap (subgroupFamily P Q) (representationFamily P Q σ τ)).ofBijective
    (finiteProductTensorMap_bijective k Index (family G H) (subgroupFamily P Q)
      (family V W) (representationFamily P Q σ τ))
  exact Representation.Equiv.mk e.toLinearEquiv
    (fun g => e.isIntertwining' (groupEquiv G H g))

/-- Smooth induction on a binary product is the external tensor of the inductions. -/
def commonEquiv :
    (external (smoothInduced P σ) (smoothInduced Q τ)).Equiv
      (smoothInduced (P.prod Q) (inducing P Q σ τ)) :=
  ((inducedTensorEquiv P Q σ τ).trans (finiteEquiv P Q σ τ)).trans
    (productInducedEquiv P Q σ τ)

@[simp] theorem commonEquiv_tmul_eval (f : SmoothFunctions P σ) (h : SmoothFunctions Q τ) (g : G × H) :
    eval (P.prod Q) (inducing P Q σ τ) (commonEquiv P Q σ τ (f ⊗ₜ[k] h)) g =
      eval P σ f g.1 ⊗ₜ[k] eval Q τ h g.2 := by
  let N := fun i => SmoothFunctions (subgroupFamily P Q i) (representationFamily P Q σ τ i)
  let F : ∀ i, N i := fun | .inl _ => f | .inr _ => h
  change (tensorEquiv k V W).symm
    (eval _ _ (finiteProductTensorMap (subgroupFamily P Q) (representationFamily P Q σ τ)
      (tensorEquivDep k N (f ⊗ₜ[k] h))) (groupEquiv G H g)) = _
  rw [show tensorEquivDep k N (f ⊗ₜ[k] h) = PiTensorProduct.tprod k F from
    tensorEquivDep_tprod k N F, finiteProductTensorMap_tprod_eval]
  apply (tensorEquiv k V W).injective
  rw [LinearEquiv.apply_symm_apply, tensorEquiv_tmul]
  congr 1
  funext i
  cases i <;> rfl

end Field

end Langlands.Induction.BinaryTensor

namespace Langlands.Induction.BinaryTensor

section Lift

universe uR uG uV uX uY

variable {R : Type uR} [CommRing R] {G : Type uG} [Group G]
variable {V : Type uV} [AddCommGroup V] [Module R V]

/-- Raise the ambient group universe by the usual up/down isomorphism. -/
def liftGroupEquiv (G : Type uG) [Group G] [TopologicalSpace G] : G ≃ₜ* ULift.{uX} G where
  toMulEquiv := MulEquiv.ulift.symm
  continuous_toFun := continuous_uliftUp
  continuous_invFun := continuous_uliftDown

/-- Lift an actual subgroup by inverse image under down. -/
abbrev liftSubgroup (P : Subgroup G) : Subgroup (ULift.{uX} G) :=
  P.comap MulEquiv.ulift.toMonoidHom

/-- The subgroup up/down isomorphism. -/
def liftSubgroupEquiv (P : Subgroup G) : P ≃* liftSubgroup.{uG, uX} P where
  toFun p := ⟨ULift.up p.1, p.2⟩
  invFun p := ⟨p.1.down, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- Lift the inducing carrier and pull the subgroup action back along down. -/
def liftRepresentation (P : Subgroup G) (σ : Representation R P V) :
    Representation R (liftSubgroup.{uG, uX} P) (ULift.{uY} V) :=
  (ULift.moduleEquiv (R := R) (M := V)).symm.conjRingEquiv.toMonoidHom.comp
    (σ.comp (liftSubgroupEquiv P).symm.toMonoidHom)

variable [TopologicalSpace G]

/-- Actual left quotients are preserved by the universe lift. -/
def liftQuotientEquiv (P : Subgroup G) :
    LeftQuotient P ≃ₜ LeftQuotient (liftSubgroup.{uG, uX} P) :=
  Homeomorph.Quotient.congr (liftGroupEquiv G).toHomeomorph (by
    intro x y
    simp only [QuotientGroup.rightRel_apply]
    rfl)

instance liftCompactQuotient (P : Subgroup G) [CompactSpace (LeftQuotient P)] :
    CompactSpace (LeftQuotient (liftSubgroup.{uG, uX} P)) :=
  (liftQuotientEquiv P).compactSpace

instance liftNonarchimedean [NonarchimedeanGroup G] : NonarchimedeanGroup (ULift.{uX} G) :=
  NonarchimedeanGroup.nonarchimedean_of_emb (liftGroupEquiv G).toMonoidHom
    (liftGroupEquiv G).toHomeomorph.isOpenEmbedding

instance liftWeaklyLocallyCompact [WeaklyLocallyCompactSpace G] :
    WeaklyLocallyCompactSpace (ULift.{uX} G) :=
  Topology.IsClosedEmbedding.uliftDown.weaklyLocallyCompactSpace

variable [IsTopologicalGroup G]

/-- Universe lifting preserves smooth induction, by pre- and postcomposition. -/
def liftInducedEquiv (P : Subgroup G) (σ : Representation R P V) :
    Representation.Equiv ((smoothInduced (liftSubgroup.{uG, uX} P)
      (liftRepresentation.{uR, uG, uV, uX, uY} P σ)).comp (liftGroupEquiv G).toMonoidHom)
      (smoothInduced P σ) :=
  (precomposeSmoothInducedGroupEquiv
    (σ := liftRepresentation.{uR, uG, uV, uX, uY} P σ)
    (liftGroupEquiv G) (liftSubgroupEquiv P)
    (fun _ => rfl) (fun _ => rfl)).trans
    (smoothInducedEquiv P (Representation.Equiv.mk
      (ρ := (liftRepresentation.{uR, uG, uV, uX, uY} P σ).comp
        (liftSubgroupEquiv P).toMonoidHom)
      (σ := σ) ULift.moduleEquiv (fun p => by ext v; rfl)))

@[simp] theorem liftInducedEquiv_eval (P : Subgroup G) (σ : Representation R P V)
    (f : SmoothFunctions (liftSubgroup.{uG, uX} P)
      (liftRepresentation.{uR, uG, uV, uX, uY} P σ)) (g : G) :
    eval P σ (liftInducedEquiv P σ f) g = (eval _ _ f (ULift.up g)).down := rfl

@[simp] theorem liftInducedEquiv_symm_eval (P : Subgroup G) (σ : Representation R P V)
    (f : SmoothFunctions P σ) (g : G) :
    eval (liftSubgroup.{uG, uX} P) (liftRepresentation.{uR, uG, uV, uX, uY} P σ)
      ((liftInducedEquiv P σ).symm f) (ULift.up g) = ULift.up (eval P σ f g) := rfl

end Lift

section Independent

universe uR uG uH uV uW

variable {R : Type uR} [CommRing R]
variable {G : Type uG} {H : Type uH} [Group G] [Group H]
variable [TopologicalSpace G] [TopologicalSpace H]
variable {V : Type uV} {W : Type uW}
variable [AddCommGroup V] [AddCommGroup W] [Module R V] [Module R W]
variable (P : Subgroup G) (Q : Subgroup H)
variable (σ : Representation R P V) (τ : Representation R Q W)

/-- Lift both group universes to their common maximum. -/
def liftProductGroupEquiv : G × H ≃ₜ* (ULift.{uH} G × ULift.{uG} H) where
  toMulEquiv := MulEquiv.prodCongr MulEquiv.ulift.symm MulEquiv.ulift.symm
  continuous_toFun := (continuous_uliftUp.comp continuous_fst).prodMk
    (continuous_uliftUp.comp continuous_snd)
  continuous_invFun := (continuous_uliftDown.comp continuous_fst).prodMk
    (continuous_uliftDown.comp continuous_snd)

/-- The up maps preserve the actual product subgroup. -/
def liftProductSubgroupEquiv :
    P.prod Q ≃* (liftSubgroup.{uG, uH} P).prod (liftSubgroup.{uH, uG} Q) :=
  (P.prodEquiv Q).trans
    ((MulEquiv.prodCongr (liftSubgroupEquiv P) (liftSubgroupEquiv Q)).trans
      ((liftSubgroup P).prodEquiv (liftSubgroup Q)).symm)

/-- Lower both tensor factors after raising them to a common carrier universe. -/
def downTensorEquiv : (ULift.{uW} V ⊗[R] ULift.{uV} W) ≃ₗ[R] (V ⊗[R] W) :=
  TensorProduct.congr ULift.moduleEquiv ULift.moduleEquiv

/-- Tensor down intertwines the lifted product inducing action. -/
def liftProductInducingEquiv :
    Representation.Equiv
      ((inducing (liftSubgroup.{uG, uH} P) (liftSubgroup.{uH, uG} Q)
        (liftRepresentation.{uR, uG, uV, uH, uW} P σ)
        (liftRepresentation.{uR, uH, uW, uG, uV} Q τ)).comp
          (liftProductSubgroupEquiv P Q).toMonoidHom)
      (inducing P Q σ τ) where
  toLinearEquiv := downTensorEquiv
  isIntertwining' p := by
    ext v w
    rfl

variable [IsTopologicalGroup G] [IsTopologicalGroup H]

/-- Lower a lifted product induction using actual pre- and postcomposition. -/
def liftProductInducedEquiv :
    Representation.Equiv
      ((smoothInduced ((liftSubgroup.{uG, uH} P).prod (liftSubgroup.{uH, uG} Q))
        (inducing (liftSubgroup.{uG, uH} P) (liftSubgroup.{uH, uG} Q)
          (liftRepresentation.{uR, uG, uV, uH, uW} P σ)
          (liftRepresentation.{uR, uH, uW, uG, uV} Q τ))).comp
        liftProductGroupEquiv.toMonoidHom)
      (smoothInduced (P.prod Q) (inducing P Q σ τ)) :=
  (precomposeSmoothInducedGroupEquiv
    (σ := inducing (liftSubgroup.{uG, uH} P) (liftSubgroup.{uH, uG} Q)
      (liftRepresentation.{uR, uG, uV, uH, uW} P σ)
      (liftRepresentation.{uR, uH, uW, uG, uV} Q τ))
    liftProductGroupEquiv (liftProductSubgroupEquiv P Q)
    (fun _ => rfl) (fun _ => rfl)).trans
      (smoothInducedEquiv (P.prod Q) (liftProductInducingEquiv P Q σ τ))

/-- Lower both induced factors, equivariantly for the ordinary binary group. -/
def liftExternalInducedEquiv :
    Representation.Equiv
      ((external
        (smoothInduced (liftSubgroup.{uG, uH} P)
          (liftRepresentation.{uR, uG, uV, uH, uW} P σ))
        (smoothInduced (liftSubgroup.{uH, uG} Q)
          (liftRepresentation.{uR, uH, uW, uG, uV} Q τ))).comp
        liftProductGroupEquiv.toMonoidHom)
      (external (smoothInduced P σ) (smoothInduced Q τ)) where
  toLinearEquiv := TensorProduct.congr
    (liftInducedEquiv.{uR, uG, uV, uH, uW} P σ).toLinearEquiv
    (liftInducedEquiv.{uR, uH, uW, uG, uV} Q τ).toLinearEquiv
  isIntertwining' g := by
    ext f h
    rfl

end Independent

section FieldIndependent

universe uR uG uH uV uW

variable {k : Type uR} [Field k]
variable {G : Type uG} {H : Type uH} [Group G] [Group H]
variable [TopologicalSpace G] [TopologicalSpace H]
variable {V : Type uV} {W : Type uW}
variable [AddCommGroup V] [AddCommGroup W] [Module k V] [Module k W]
variable (P : Subgroup G) (Q : Subgroup H)
variable (σ : Representation k P V) (τ : Representation k Q W)
variable [NonarchimedeanGroup G] [NonarchimedeanGroup H]
variable [WeaklyLocallyCompactSpace G] [WeaklyLocallyCompactSpace H]
variable [CompactSpace (LeftQuotient P)] [CompactSpace (LeftQuotient Q)]

/-- Binary induction tensor equivalence with independent group and carrier universes. -/
def equiv :
    (external (smoothInduced P σ) (smoothInduced Q τ)).Equiv
      (smoothInduced (P.prod Q) (inducing P Q σ τ)) := by
  let e := commonEquiv (liftSubgroup.{uG, uH} P) (liftSubgroup.{uH, uG} Q)
    (liftRepresentation.{uR, uG, uV, uH, uW} P σ)
    (liftRepresentation.{uR, uH, uW, uG, uV} Q τ)
  let e' := pullEquiv e liftProductGroupEquiv.toMonoidHom
  exact ((liftExternalInducedEquiv P Q σ τ).symm.trans e').trans
    (liftProductInducedEquiv P Q σ τ)

@[simp] theorem equiv_tmul_eval
    (f : SmoothFunctions P σ) (h : SmoothFunctions Q τ) (g : G × H) :
    eval (P.prod Q) (inducing P Q σ τ) (equiv P Q σ τ (f ⊗ₜ[k] h)) g =
      eval P σ f g.1 ⊗ₜ[k] eval Q τ h g.2 := by
  change downTensorEquiv
    (eval _ _ (commonEquiv (liftSubgroup.{uG, uH} P) (liftSubgroup.{uH, uG} Q)
      (liftRepresentation.{uR, uG, uV, uH, uW} P σ)
      (liftRepresentation.{uR, uH, uW, uG, uV} Q τ)
      ((liftExternalInducedEquiv P Q σ τ).symm (f ⊗ₜ[k] h)))
      (liftProductGroupEquiv g)) = _
  change downTensorEquiv
    (eval _ _ (commonEquiv _ _ _ _
      ((liftInducedEquiv P σ).symm f ⊗ₜ[k] (liftInducedEquiv Q τ).symm h))
      (liftProductGroupEquiv g)) = _
  rw [commonEquiv_tmul_eval]
  rfl

end FieldIndependent

end Langlands.Induction.BinaryTensor
