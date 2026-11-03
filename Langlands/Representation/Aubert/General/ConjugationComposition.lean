import Langlands.Representation.Aubert.General.Parabolic

/-! # Composition, inverse and inner comparisons for actual conjugation transport -/

noncomputable section

open CategoryTheory

namespace Langlands.Aubert.General

universe uG uV

variable {G : Type uG} [Group G] {M N L : Subgroup G}

/-- Reverse the actual subgroup membership equivalence using the inverse element. -/
theorem conjugationMembership_inv (g : G)
    (hMN : ∀ x : G, x ∈ N ↔ g⁻¹ * x * g ∈ M) :
    ∀ x : G, x ∈ M ↔ (g⁻¹)⁻¹ * x * g⁻¹ ∈ N := by
  intro x
  simpa [mul_assoc] using (hMN (g * x * g⁻¹)).symm

/-- Composing transport by `g` and then by `f` uses the same actual element `f * g`. -/
theorem conjugationMembership_mul (g f : G)
    (hMN : ∀ x : G, x ∈ N ↔ g⁻¹ * x * g ∈ M)
    (hNL : ∀ x : G, x ∈ L ↔ f⁻¹ * x * f ∈ N) :
    ∀ x : G, x ∈ L ↔ (f * g)⁻¹ * x * (f * g) ∈ M := by
  intro x
  simpa only [mul_inv_rev, mul_assoc] using (hNL x).trans (hMN (f⁻¹ * x * f))

/-- An element of a subgroup conjugates that subgroup to itself. -/
theorem conjugationMembership_inner (m : M) :
    ∀ x : G, x ∈ M ↔ (m : G)⁻¹ * x * (m : G) ∈ M := by
  intro x
  constructor
  · intro hx
    exact M.mul_mem (M.mul_mem (M.inv_mem m.property) hx) m.property
  · intro hx
    have h := M.mul_mem (M.mul_mem m.property hx) (M.inv_mem m.property)
    simpa [mul_assoc] using h

variable [TopologicalSpace G] [IsTopologicalGroup G]

/-- The identity linear map compares two successive transports with transport
by their product. No quotient of the group of conjugating elements is used. -/
def conjugationFunctorCompIsoApp (g f : G)
    (hMN : ∀ x : G, x ∈ N ↔ g⁻¹ * x * g ∈ M)
    (hNL : ∀ x : G, x ∈ L ↔ f⁻¹ * x * f ∈ N)
    (A : SmoothRep.{0, uG, uV} ℂ M) :
    (conjugationFunctor f hNL).obj ((conjugationFunctor g hMN).obj A) ≅
      (conjugationFunctor (f * g) (conjugationMembership_mul g f hMN hNL)).obj A :=
  SmoothRep.mkIso (Representation.Equiv.mk (LinearEquiv.refl ℂ A) fun x => by
    have hx : conjugationEquiv g hMN (conjugationEquiv f hNL x) =
        conjugationEquiv (f * g) (conjugationMembership_mul g f hMN hNL) x := by
      apply Subtype.ext
      simp only [conjugationEquiv_apply, mul_inv_rev, mul_assoc]
    ext v
    change A.representation (conjugationEquiv g hMN (conjugationEquiv f hNL x)) v =
      A.representation
        (conjugationEquiv (f * g) (conjugationMembership_mul g f hMN hNL) x) v
    rw [hx])

/-- The product comparison is natural for actual equivariant linear maps. -/
def conjugationFunctorCompIso (g f : G)
    (hMN : ∀ x : G, x ∈ N ↔ g⁻¹ * x * g ∈ M)
    (hNL : ∀ x : G, x ∈ L ↔ f⁻¹ * x * f ∈ N) :
    conjugationFunctor.{uG, uV} g hMN ⋙ conjugationFunctor f hNL ≅
      conjugationFunctor (f * g) (conjugationMembership_mul g f hMN hNL) :=
  NatIso.ofComponents (conjugationFunctorCompIsoApp g f hMN hNL) (fun _ => by
    apply ObjectProperty.hom_ext
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    rfl)

/-- Inverse transport after transport is compared with the original object by
the identity linear map. -/
def conjugationFunctorInvIsoApp (g : G)
    (hMN : ∀ x : G, x ∈ N ↔ g⁻¹ * x * g ∈ M)
    (A : SmoothRep.{0, uG, uV} ℂ M) :
    (conjugationFunctor g⁻¹ (conjugationMembership_inv g hMN)).obj
        ((conjugationFunctor g hMN).obj A) ≅ A :=
  SmoothRep.mkIso (Representation.Equiv.mk (LinearEquiv.refl ℂ A) fun x => by
    have hx : conjugationEquiv g hMN
        (conjugationEquiv g⁻¹ (conjugationMembership_inv g hMN) x) = x := by
      apply Subtype.ext
      simp [conjugationEquiv_apply, mul_assoc]
    ext v
    change A.representation (conjugationEquiv g hMN
      (conjugationEquiv g⁻¹ (conjugationMembership_inv g hMN) x)) v = A.representation x v
    rw [hx])

/-- Inner transport is intertwined with the original action by `A(m)`. -/
def conjugationFunctorInnerIso (m : M) (A : SmoothRep.{0, uG, uV} ℂ M) :
    (conjugationFunctor (m : G) (conjugationMembership_inner m)).obj A ≅ A :=
  SmoothRep.mkIso (Representation.Equiv.mk
    (LinearMap.GeneralLinearGroup.toLinearEquiv (A.representation.asGroupHom m)) fun x => by
      have hx : conjugationEquiv (m : G) (conjugationMembership_inner m) x = m⁻¹ * x * m :=
        Subtype.ext rfl
      have h : A.representation m * A.representation (m⁻¹ * x * m) =
          A.representation x * A.representation m := by
        rw [← map_mul, ← map_mul]
        congr 1
        simp [mul_assoc]
      ext v
      change A at v
      change A.representation m
          (A.representation (conjugationEquiv (m : G) (conjugationMembership_inner m) x) v) =
        A.representation x (A.representation m v)
      rw [hx]
      exact congrArg (fun T : Module.End ℂ A => T v) h)

/-- Compose actual isomorphisms of conjugate data, retaining the product element. -/
def conjugationDataIsoTrans (g f : G)
    (hMN : ∀ x : G, x ∈ N ↔ g⁻¹ * x * g ∈ M)
    (hNL : ∀ x : G, x ∈ L ↔ f⁻¹ * x * f ∈ N)
    {A : SmoothRep.{0, uG, uV} ℂ M} {B : SmoothRep.{0, uG, uV} ℂ N}
    {C : SmoothRep.{0, uG, uV} ℂ L}
    (e : B ≅ (conjugationFunctor g hMN).obj A)
    (e' : C ≅ (conjugationFunctor f hNL).obj B) :
    C ≅ (conjugationFunctor (f * g) (conjugationMembership_mul g f hMN hNL)).obj A :=
  e' ≪≫ (conjugationFunctor f hNL).mapIso e ≪≫ conjugationFunctorCompIsoApp g f hMN hNL A

/-- Reverse an actual isomorphism of conjugate data using the inverse element. -/
def conjugationDataIsoSymm (g : G)
    (hMN : ∀ x : G, x ∈ N ↔ g⁻¹ * x * g ∈ M)
    {A : SmoothRep.{0, uG, uV} ℂ M} {B : SmoothRep.{0, uG, uV} ℂ N}
    (e : B ≅ (conjugationFunctor g hMN).obj A) :
    A ≅ (conjugationFunctor g⁻¹ (conjugationMembership_inv g hMN)).obj B :=
  ((conjugationFunctor g⁻¹ (conjugationMembership_inv g hMN)).mapIso e ≪≫
    conjugationFunctorInvIsoApp g hMN A).symm

end Langlands.Aubert.General
