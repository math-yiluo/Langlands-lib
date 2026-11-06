import Langlands.GroupScheme.Rational.LeviRetraction
import Langlands.GroupScheme.Reductive.ToPseudoReductive
import Langlands.GroupScheme.Dynamic.CentralizerReductiveTransport

/-! # Rational Levi inclusions into a full reductive group -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
  {G P M : GroupScheme (Spec (CommRingCat.of k))}

/-- A rational Levi inclusion into a connected reductive group is an
isomorphism: its complementary unipotent radical is trivial. -/
theorem IsRationalLeviSubgroup.isIso_of_connectedReductive
    {l : M ⟶ P} (hl : IsRationalLeviSubgroup l)
    (hP : IsConnectedReductive P) : IsIso l := by
  obtain ⟨U, r, hr, hmul⟩ := hl.exists_unipotentRadical
  let : IsIso (subgroupMultiplication l r) := hmul
  have hrad : SubgroupFunctor.range r = ⊥ :=
    hP.hasTrivialUnipotentRadical U r hr.1.isClosedSubgroup hr.1.smooth
      hr.1.connectedSpace hr.1.isUnipotent hr.1.isNormal
  refine ⟨⟨leviRetraction l r hr.1.isNormal,
    levi_comp_leviRetraction l r hr.1.isNormal, ?_⟩⟩
  apply hom_ext_points
  intro T x
  rw [Grp.comp_hom_hom, ← Category.assoc, comp_leviRetraction,
    Grp.id_hom_hom, Category.comp_id]
  have hx : radicalComponent l r x ≫ r.hom.hom = 1 := by
    have hmem : radicalComponent l r x ≫ r.hom.hom ∈
        (SubgroupFunctor.range r).carrier T :=
      SubgroupFunctor.mem_range.mpr ⟨_, rfl⟩
    rw [hrad] at hmem
    exact hmem
  simpa only [hx, mul_one] using leviComponent_mul_radicalComponent l r x

/-- The actual isomorphism whose forward map is the original rational Levi
inclusion into a connected reductive group. -/
def IsRationalLeviSubgroup.isoOfConnectedReductive
    {l : M ⟶ P} (hl : IsRationalLeviSubgroup l)
    (hP : IsConnectedReductive P) : M ≅ P :=
  haveI := hl.isIso_of_connectedReductive hP
  asIso l

@[simp] theorem IsRationalLeviSubgroup.isoOfConnectedReductive_hom
    {l : M ⟶ P} (hl : IsRationalLeviSubgroup l)
    (hP : IsConnectedReductive P) :
    (hl.isoOfConnectedReductive hP).hom = l := rfl

/-- If a parabolic inclusion is an isomorphism onto a connected reductive
group, its rational Levi inclusion is itself an isomorphism. -/
theorem IsRationalLeviSubgroup.isIso_of_isIso_parabolic
    {p : P ⟶ G} [IsIso p] {l : M ⟶ P}
    (hl : IsRationalLeviSubgroup l) (hG : IsConnectedReductive G) : IsIso l :=
  hl.isIso_of_connectedReductive (hG.of_iso (asIso p))

/-- A rational Levi of a full parabolic is isomorphic to the original
ambient group, through the given composite inclusion. -/
def IsRationalLeviSubgroup.isoOfIsIsoParabolic
    {p : P ⟶ G} [IsIso p] {l : M ⟶ P}
    (hl : IsRationalLeviSubgroup l) (hG : IsConnectedReductive G) : M ≅ G :=
  haveI := hl.isIso_of_isIso_parabolic (p := p) hG
  asIso (l ≫ p)

@[simp] theorem IsRationalLeviSubgroup.isoOfIsIsoParabolic_hom
    {p : P ⟶ G} [IsIso p] {l : M ⟶ P}
    (hl : IsRationalLeviSubgroup l) (hG : IsConnectedReductive G) :
    (hl.isoOfIsIsoParabolic (p := p) hG).hom = l ≫ p := rfl

/-- Extend an isomorphism of intersection Levis to the two full Levis when
both intersection parabolics are full. The resulting map satisfies the
original ambient conjugacy equation, in the reverse direction. -/
def rationalLeviConjugacyOfFullParabolics
    {P₁ P₂ L₁ L₂ M₁ M₂ : GroupScheme (Spec (CommRingCat.of k))}
    {p₁ : P₁ ⟶ M₁} [IsIso p₁] {p₂ : P₂ ⟶ M₂} [IsIso p₂]
    {l₁ : L₁ ⟶ P₁} {l₂ : L₂ ⟶ P₂}
    (hl₁ : IsRationalLeviSubgroup l₁) (hl₂ : IsRationalLeviSubgroup l₂)
    (hM₁ : IsConnectedReductive M₁) (hM₂ : IsConnectedReductive M₂)
    (m₁ : M₁ ⟶ G) (m₂ : M₂ ⟶ G) (a : G ≅ G) (φ : L₂ ≅ L₁)
    (hφ : φ.hom ≫ l₁ ≫ p₁ ≫ m₁ = l₂ ≫ p₂ ≫ m₂ ≫ a.hom) :
    {e : M₁ ≅ M₂ // e.hom ≫ m₂ = m₁ ≫ a.inv} := by
  let α := hl₁.isoOfIsIsoParabolic (p := p₁) hM₁
  let β := hl₂.isoOfIsIsoParabolic (p := p₂) hM₂
  refine ⟨α.symm ≪≫ φ.symm ≪≫ β, ?_⟩
  apply (cancel_epi α.hom).mp
  have hφ' : φ.hom ≫ α.hom ≫ m₁ = β.hom ≫ m₂ ≫ a.hom := hφ
  have h := congrArg (fun f : L₂ ⟶ G => φ.inv ≫ f ≫ a.inv) hφ'
  simpa only [Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.inv_hom_id_assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id]
    using h.symm

end Langlands.GroupScheme
