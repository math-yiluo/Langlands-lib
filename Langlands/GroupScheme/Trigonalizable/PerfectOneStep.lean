import Langlands.GroupScheme.Trigonalizable.CorrectionOfSolvable
import Langlands.GroupScheme.Trigonalizable.PerfectCorrection
import Langlands.GroupScheme.LinearAdditiveExtension.Section
import Langlands.GroupScheme.LinearKernelTowerSection

/-! # One-step splitting and tower sections over arbitrary fields -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.TrigonalizableExtensionSplit

open LinearAdditiveExtension LinearKernelTower

section OneStep

variable {k : Type u} [Field k] {Λ : Type u} [AddCommGroup Λ]

/-- **One step, over any field.** The splitting theorem `linearAdditiveExtensionSplitting`
(Milne 15.34(d)) holds over every field once the correction equation is solvable. -/
theorem exists_section_of_solvable
    {E : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom E.X.hom]
    (q : E ⟶ (Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp)
    (hflat : Flat q.hom.hom.left) (hsurj : Surjective q.hom.hom.left)
    (a : kernel q ⟶ VectorGroup.groupScheme (CommRingCat.of k) 1) (ha : IsClosedSubgroup a)
    (χ : characterLattice (Diagonalizable.groupScheme (CommRingCat.of k) Λ))
    (b : AutomorphicAction (Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp (kernel q))
    (hconj : ∀ (T : Over (Spec (CommRingCat.of k))) (g : T ⟶ E.X) (x : T ⟶ (kernel q).X),
      b.act (g ≫ q.hom.hom) x ≫ (kernelι q).hom.hom = g * (x ≫ (kernelι q).hom.hom) * g⁻¹)
    (hlin : ∀ (T : Over (Spec (CommRingCat.of k)))
      (d : T ⟶ (Diagonalizable.groupScheme (CommRingCat.of k) Λ).X) (x : T ⟶ (kernel q).X),
      b.act d x ≫ a.hom.hom = (VectorGroup.weightAction (n := 1) χ).act d (x ≫ a.hom.hom))
    (hsolv : ClosedAdditivePolynomial.closedPolynomial a ≠ 0 →
      (∀ m : k, ∃ r : k, (ClosedAdditivePolynomial.closedPolynomial a).eval r = m) ∨
        ∀ (T : Over (Spec (CommRingCat.of k)))
          (d : T ⟶ (Diagonalizable.groupScheme (CommRingCat.of k) Λ).X),
          VectorGroup.charValue χ T d ^
            (ClosedAdditivePolynomial.closedPolynomial a).natDegree = 1) :
    ∃ s : (Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp ⟶ E, s ≫ q = 𝟙 _ := by
  have : IsAffine (Diagonalizable.groupScheme (CommRingCat.of k) Λ).X.left :=
    isAffine_of_isAffineHom (Diagonalizable.groupScheme (CommRingCat.of k) Λ).X.hom
  have : IsAffine E.X.left := isAffine_of_isAffineHom E.X.hom
  have : IsAffineHom q.hom.hom.left := isAffineHom_of_isAffine _
  have : Flat q.hom.hom.left := hflat
  have : Surjective q.hom.hom.left := hsurj
  obtain ⟨fE, hfE⟩ := exists_equivariant q a χ hflat hsurj
  have hc₁ : ∀ (T : Over (Spec (CommRingCat.of k))) (g h : T ⟶ E.X),
      cd ((g * h) ≫ crossedHom q a χ b fE hconj hlin hfE) =
        cd (g ≫ crossedHom q a χ b fE hconj hlin hfE) +
          chi q χ g * cd (h ≫ crossedHom q a χ b fE hconj hlin hfE) := by
    intro T g h
    have := congrArg (fun m => cd (lift g h ≫ m)) (crossedHom_mul q a χ b fE hconj hlin hfE)
    rw [← Category.assoc, MonObj.comp_mul, lift_fst, lift_snd, MonObj.comp_mul, cd_mul,
      AutomorphicAction.naturality, cd_act, lift_fst_assoc, lift_fst_assoc,
      lift_snd_assoc] at this
    exact this
  have hc₂ : ∀ (T : Over (Spec (CommRingCat.of k))) (u : T ⟶ (kernel q).X),
      cd ((u ≫ (kernelι q).hom.hom) ≫ crossedHom q a χ b fE hconj hlin hfE) =
        cd (u ≫ a.hom.hom) := by
    intro T u
    rw [Category.assoc, kernel_comp_crossedHom q a χ b fE hconj hlin hfE ha]
  obtain ⟨c, h₁, h₂, h₃⟩ := exists_corrected_of_solvable q a χ b hlin ha hsolv _ hc₁ hc₂
  exact exists_section q a χ b hlin c h₁ h₂ ha h₃


end OneStep

variable {k : Type u} [Field k] (Λ : Type u) [AddCommGroup Λ]

variable (k) in
/-- One-step splitting for a fixed field `k` and character group `Λ`: the body of
`LinearAdditiveExtensionSplittingStatement` with `k` and `Λ` fixed and no algebraic closure. -/
def OneStepSplitting : Prop :=
  ∀ (E : GroupScheme (Spec (CommRingCat.of k)))
    [LocallyOfFiniteType E.X.hom] [IsAffineHom E.X.hom]
    (q : E ⟶ (Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp),
    Flat q.hom.hom.left → Surjective q.hom.hom.left →
    LocallyOfFinitePresentation q.hom.hom.left →
    ∀ (a : kernel q ⟶ VectorGroup.groupScheme (CommRingCat.of k) 1), IsClosedSubgroup a →
    ∀ (χ : characterLattice (Diagonalizable.groupScheme (CommRingCat.of k) Λ))
      (b : AutomorphicAction (Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp (kernel q)),
      (∀ (T : Over (Spec (CommRingCat.of k))) (g : T ⟶ E.X) (x : T ⟶ (kernel q).X),
        b.act (g ≫ q.hom.hom) x ≫ (kernelι q).hom.hom =
          g * (x ≫ (kernelι q).hom.hom) * g⁻¹) →
      (∀ (T : Over (Spec (CommRingCat.of k)))
        (d : T ⟶ (Diagonalizable.groupScheme (CommRingCat.of k) Λ).X) (x : T ⟶ (kernel q).X),
        b.act d x ≫ a.hom.hom =
          (VectorGroup.weightAction (n := 1) χ).act d (x ≫ a.hom.hom)) →
      ∃ s : (Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp ⟶ E, s ≫ q = 𝟙 _

/-- Over a perfect field with `D(Λ)` connected, one-step splitting holds. -/
theorem oneStepSplitting_of_perfect [PerfectField k]
    (hD : ConnectedSpace (Diagonalizable.groupScheme (CommRingCat.of k) Λ).X.left) :
    OneStepSplitting k Λ := by
  intro E _ _ q hflat hsurj _ a ha χ b hconj hlin
  refine exists_section_of_solvable q hflat hsurj a ha χ b hconj hlin fun hf => ?_
  exact PerfectCorrection.surjective_or_charValue_pow_eq_one a χ hD ha hf
    (fun T d x hx => weight_stable q a χ b hlin (T := T) d x hx)

variable {Λ}

/-- One step of a tower. Let `q = p ≫ r`, where `p : E ⟶ Q` is an fppf quotient by its full
kernel and this kernel is character-linear for `q`. If `r` has a homomorphic section `t`,
the one-step splitting `hsplit`, applied to the inverse image of `t` in `E`, gives a
homomorphic section of `q`. -/
theorem exists_section_of_step' (hsplit : OneStepSplitting k Λ)
    {E Q : GroupScheme (Spec (CommRingCat.of k))}
    [LocallyOfFiniteType E.X.hom] [IsAffineHom E.X.hom] [IsAffineHom Q.X.hom]
    (p : E ⟶ Q) (r : Q ⟶ (Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp)
    (hp : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range (kernelι p)) p)
    (hK : IsCharacterLinearKernel (Diagonalizable.groupScheme (CommRingCat.of k) Λ)
      (p ≫ r) p)
    (t : (Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp ⟶ Q) (ht : t ≫ r = 𝟙 _) :
    ∃ s : (Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp ⟶ E,
      s ≫ p ≫ r = 𝟙 _ := by
  obtain ⟨a, χ, b, ha, hconj, hlin⟩ := hK
  have htc : IsClosedSubgroup t := isClosedSubgroup_of_section r t ht
  -- The inverse image `E'` of the section, with inclusion `incl` and projection `π` onto `D`.
  let incl := SubgroupPreimage.inclusion p t
  let π := SubgroupPreimage.projection p t
  have hw : incl ≫ p = π ≫ t := subgroupIntersection_condition p t
  have hinclc : IsClosedSubgroup incl := SubgroupPreimage.isClosedSubgroup p t htc
  have : IsClosedImmersion incl.hom.hom.left := hinclc
  have : Mono incl.hom.hom := Over.mono_of_mono_left _
  have : IsAffineHom (SubgroupPreimage.groupScheme p t).X.hom :=
    SubgroupPreimage.isAffineHom p t htc
  have : LocallyOfFiniteType (SubgroupPreimage.groupScheme p t).X.hom := by
    rw [← Over.w incl.hom.hom]
    infer_instance
  -- The kernel of `π` is the kernel of `p`.
  have h0 : kernelι p ≫ p = 0 := SplitSolvable.kernel_comp_eq_zero hp
  let z := SubgroupPreimage.kernelInclusion p t (kernelι p) h0
  have : Mono z.hom.hom := SubgroupPreimage.kernelInclusion_mono p t (kernelι p) h0
  have hπ : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range z) π :=
    SubgroupPreimage.isFppfQuotient_projection p t (kernelι p) h0 hp
  have hz : (SubgroupFunctor.range z).IsRepresentedBy z := ⟨inferInstance, rfl⟩
  let e := hπ.kernelIso hz
  have he : e.hom ≫ kernelι π = z := hπ.kernelIso_hom_comp hz
  have hzincl : z ≫ incl = kernelι p :=
    SubgroupPreimage.kernelInclusion_comp_inclusion p t (kernelι p) h0
  have hinv : e.inv ≫ z = kernelι π := by
    rw [← he, ← Category.assoc, e.inv_hom_id, Category.id_comp]
  have hinvincl : (kernelι π).hom.hom ≫ incl.hom.hom = e.inv.hom.hom ≫ (kernelι p).hom.hom := by
    rw [← Grp.comp_hom_hom, ← Grp.comp_hom_hom, ← hinv, Category.assoc, hzincl]
  have hπt : incl ≫ p ≫ r = π := by
    rw [← Category.assoc, hw, Category.assoc, ht, Category.comp_id]
  -- Transport the linear data to the kernel of `π`.
  have ha' : IsClosedSubgroup (e.inv ≫ a) := by
    change IsClosedImmersion (e.inv.hom.hom.left ≫ a.hom.hom.left)
    have : IsClosedImmersion a.hom.hom.left := ha
    have : IsIso e.inv.hom.hom.left := by
      have : IsIso e.inv := inferInstance
      exact (Grp.forget _ ⋙ Over.forget _).map_isIso e.inv
    infer_instance
  obtain ⟨s', hs'⟩ := hsplit (SubgroupPreimage.groupScheme p t) π hπ.1 hπ.2.1 hπ.2.2.1
    (e.inv ≫ a) ha' χ (b.transportActed e)
    (by
      intro T g x
      apply (cancel_mono incl.hom.hom).mp
      have h1 : e.hom.hom.hom ≫ (kernelι π).hom.hom ≫ incl.hom.hom = (kernelι p).hom.hom := by
        rw [← hzincl, ← he]
        simp only [Grp.comp_hom_hom, Category.assoc]
      have hg : g ≫ π.hom.hom = (g ≫ incl.hom.hom) ≫ (p ≫ r).hom.hom := by
        rw [Category.assoc, ← Grp.comp_hom_hom, hπt]
      simp only [AutomorphicAction.transportActed_act, Category.assoc]
      rw [h1, hg, hconj, MonObj.mul_comp, MonObj.mul_comp, GrpObj.inv_comp]
      simp only [Category.assoc, hinvincl])
    (by
      intro T d x
      rw [AutomorphicAction.transportActed_act, Grp.comp_hom_hom, Category.assoc,
        ← Category.assoc e.hom.hom.hom, ← Grp.comp_hom_hom, e.hom_inv_id, Grp.id_hom_hom,
        Category.id_comp, hlin, Category.assoc])
  refine ⟨s' ≫ incl, ?_⟩
  rw [Category.assoc, hπt, hs']

/-- Every finite character-linear kernel tower over a diagonalizable group, over a
field, has a homomorphic section, given the one-step splitting `OneStepSplitting k Λ`. -/
theorem exists_section_of_hasTower' (hsplit : OneStepSplitting k Λ) :
    ∀ (n : ℕ) {E : GroupScheme (Spec (CommRingCat.of k))}
      (q : E ⟶ (Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp),
      HasTower (Diagonalizable.groupScheme (CommRingCat.of k) Λ) n q →
        ∃ s : (Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp ⟶ E, s ≫ q = 𝟙 _
  | 0, E, q, h => by
    have : IsIso q := h.2.2
    exact ⟨inv q, IsIso.inv_hom_id q⟩
  | n + 1, E, q, h => by
    obtain ⟨hft, haff, Q, p, r, hp, hpr, hK, hr⟩ := h
    have : LocallyOfFiniteType E.X.hom := hft
    have : IsAffineHom E.X.hom := haff
    have : IsAffineHom Q.X.hom := hr.isAffineHom
    obtain ⟨t, ht⟩ := exists_section_of_hasTower' hsplit n r hr
    subst hpr
    exact exists_section_of_step' hsplit p r hp hK t ht

/-- A homomorphism that admits a finite character-linear kernel tower has a homomorphic
section, given `OneStepSplitting k Λ`. -/
theorem exists_section_of_admitsTower' (hsplit : OneStepSplitting k Λ)
    {E : GroupScheme (Spec (CommRingCat.of k))}
    {q : E ⟶ (Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp}
    (h : AdmitsTower (Diagonalizable.groupScheme (CommRingCat.of k) Λ) q) :
    ∃ s : (Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp ⟶ E, s ≫ q = 𝟙 _ := by
  obtain ⟨n, hn⟩ := h
  exact exists_section_of_hasTower' hsplit n q hn


end Langlands.GroupScheme.TrigonalizableExtensionSplit
