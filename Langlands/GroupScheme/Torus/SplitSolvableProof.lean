import Langlands.GroupScheme.Torus.SplitSolvableStatement
import Langlands.GroupScheme.Torus.SplitReductiveProof
import Langlands.GroupScheme.Rational.SplitUnipotentTransport
import Langlands.GroupScheme.FieldSeparatedProof
import Langlands.GroupScheme.Absolute.BorelTransport
import Langlands.GroupScheme.Torus.Products
import Mathlib.Data.Fintype.Option

/-! # Every split torus is split solvable -/

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace SplitSolvable

variable {k : Type u} [Field k]
    {H H' : GroupScheme (Spec (CommRingCat.of k))}

/-- A Ga/Gm series transports along an actual group-scheme isomorphism. -/
theorem HasSeries.of_iso (e : H ≅ H') {n : ℕ}
    (h : HasSeries n H) : HasSeries n H' := by
  cases n with
  | zero =>
    apply SubgroupFunctor.ext
    intro T
    ext x
    rw [SubgroupFunctor.bot_carrier, Subgroup.mem_bot]
    constructor
    · intro _
      have hx : x ≫ e.inv.hom.hom ∈ (SubgroupFunctor.range (𝟙 H)).carrier T :=
        SubgroupFunctor.mem_range.mpr
          ⟨x ≫ e.inv.hom.hom, by
            change (x ≫ e.inv.hom.hom) ≫ 𝟙 H.X = _
            exact Category.comp_id _⟩
      rw [h, SubgroupFunctor.bot_carrier, Subgroup.mem_bot] at hx
      apply (isoPointsEquiv e.symm T).injective
      simpa only [isoPointsEquiv_apply, Iso.symm_hom, MonObj.one_comp] using hx
    · rintro rfl
      exact Subgroup.one_mem _
  | succ n =>
    obtain ⟨K, V, j, q, hj, hs, hc, hn, hq, hV, hK⟩ := h
    refine ⟨K, V, j ≫ e.hom, e.inv ≫ q, ?_, hs, hc, ?_, ?_, hV, hK⟩
    · have : IsIso e.hom.hom.hom.left :=
        (inferInstance : IsIso (((Grp.forget _) ⋙ Over.forget _).map e.hom))
      have : IsClosedImmersion j.hom.hom.left := hj
      change IsClosedImmersion (j.hom.hom.left ≫ e.hom.hom.hom.left)
      infer_instance
    · rw [SubgroupFunctor.range_comp_iso]
      exact hn.comap e.inv
    · rw [SubgroupFunctor.range_comp_iso]
      exact hq.comapIso e

end SplitSolvable

section Products
variable {k : Type u} [Field k]
variable (A B : GroupScheme (Spec (CommRingCat.of k)))

/-- The inclusion of the first factor is a closed subgroup over a field. -/
theorem splitSeries_product_inclusion_closed :
    IsClosedSubgroup (lift (𝟙 A) (0 : A ⟶ B)) := by
  have : IsSeparated B.X.hom := fieldSeparated k B
  have : IsSeparated (fst A.X B.X).left := by
    change IsSeparated (pullback.fst A.X.hom B.X.hom)
    infer_instance
  have he : (lift (𝟙 A) (0 : A ⟶ B)).hom.hom.left ≫
      (fst A.X B.X).left = 𝟙 A.X.left := by
    change ((lift (𝟙 A) (0 : A ⟶ B)) ≫ fst A B).hom.hom.left = _
    simp only [lift_fst, Grp.id_hom_hom, Over.id_left]
  have : IsClosedImmersion ((lift (𝟙 A) (0 : A ⟶ B)).hom.hom.left ≫
      (fst A.X B.X).left) := by rw [he]; infer_instance
  exact IsClosedImmersion.of_comp _ (fst A.X B.X).left

/-- The first inclusion is precisely the kernel of the second projection on every test. -/
theorem splitSeries_product_kernel :
    SubgroupFunctor.range (kernelι (snd A B)) =
      SubgroupFunctor.range (lift (𝟙 A) (0 : A ⟶ B)) := by
  apply SubgroupFunctor.ext
  intro T
  ext x
  rw [mem_range_kernelι_iff, SubgroupFunctor.mem_range]
  constructor
  · intro hx
    refine ⟨x ≫ fst A.X B.X, ?_⟩
    apply (productPointsEquiv A B T).injective
    apply Prod.ext
    · change ((x ≫ fst A.X B.X) ≫ (lift (𝟙 A) (0 : A ⟶ B)).hom.hom) ≫
        fst A.X B.X = x ≫ fst A.X B.X
      simp [Grp.lift_hom, Mon.lift_hom]
    · change ((x ≫ fst A.X B.X) ≫ (lift (𝟙 A) (0 : A ⟶ B)).hom.hom) ≫
        snd A.X B.X = x ≫ snd A.X B.X
      simpa [Grp.lift_hom, Mon.lift_hom, CategoryTheory.Hom.one_def] using hx.symm
  · rintro ⟨y, rfl⟩
    simp [Grp.lift_hom, Mon.lift_hom, CategoryTheory.Hom.one_def]

/-- A smooth first factor makes the second projection an actual fppf quotient. -/
theorem splitSeries_product_quotient (hs : Smooth A.X.hom) :
    RelativeRoot.IsFppfQuotient
      (SubgroupFunctor.range (lift (𝟙 A) (0 : A ⟶ B))) (snd A B) := by
  have : Smooth A.X.hom := hs
  have : Smooth (snd A B).hom.hom.left := by
    change Smooth (pullback.snd A.X.hom B.X.hom)
    infer_instance
  refine ⟨inferInstance, ?_, inferInstance, splitSeries_product_kernel A B⟩
  have he : (lift (0 : B ⟶ A) (𝟙 B)).hom.hom.left ≫
      (snd A B).hom.hom.left = 𝟙 B.X.left := by
    change ((lift (0 : B ⟶ A) (𝟙 B)) ≫ snd A B).hom.hom.left = _
    simp only [lift_snd, Grp.id_hom_hom, Over.id_left]
  have : Surjective ((lift (0 : B ⟶ A) (𝟙 B)).hom.hom.left ≫
      (snd A B).hom.hom.left) := by rw [he]; infer_instance
  exact Surjective.of_comp (lift (0 : B ⟶ A) (𝟙 B)).hom.hom.left
    (snd A B).hom.hom.left

/-- The first factor is normal on every relative test. -/
theorem splitSeries_product_inclusion_normal :
    (SubgroupFunctor.range (lift (𝟙 A) (0 : A ⟶ B))).IsNormal := by
  rw [← splitSeries_product_kernel]
  intro T g x _ hx
  rw [mem_range_kernelι_iff] at hx ⊢
  rw [MonObj.mul_comp, MonObj.mul_comp, GrpObj.inv_comp, hx, mul_one,
    mul_inv_cancel]

end Products

namespace SplitSolvable

variable {k : Type u} [Field k]
    {H : GroupScheme (Spec (CommRingCat.of k))}

/-- The empty product has a length-zero series on every relative test. -/
theorem hasSeries_splitTorus_empty (I : Type u) [Finite I] [IsEmpty I] :
    HasSeries 0 (splitTorus (Spec (CommRingCat.of k)) I) := by
  apply SubgroupFunctor.ext
  intro T
  ext x
  rw [SubgroupFunctor.bot_carrier, Subgroup.mem_bot]
  constructor
  · intro _
    apply (splitTorus.pointsEquiv I T).injective
    funext i
    exact isEmptyElim i
  · rintro rfl
    exact Subgroup.one_mem _

/-- Add one multiplicative quotient to a series. -/
theorem HasSeries.tensor_gm {n : ℕ} (hH : IsSplitTorus H) (h : HasSeries n H) :
    HasSeries (n + 1) (H ⊗ (Gm (Spec (CommRingCat.of k))).toGrp) := by
  let B := (Gm (Spec (CommRingCat.of k))).toGrp
  exact HasSeries.succ (lift (𝟙 H) (0 : H ⟶ B)) (snd H B)
    (splitSeries_product_inclusion_closed H B) hH.smooth hH.connectedSpace
    (splitSeries_product_inclusion_normal H B)
    (splitSeries_product_quotient H B hH.smooth)
    (Or.inr ⟨Iso.refl _⟩) h

/-- Every finite product of multiplicative groups has a finite represented series. -/
theorem exists_hasSeries_splitTorus (I : Type u) [Finite I] :
    ∃ n, HasSeries n (splitTorus (Spec (CommRingCat.of k)) I) := by
  refine Finite.induction_empty_option
    (P := fun J => ∀ (_ : Finite J),
      ∃ n, HasSeries n (splitTorus (Spec (CommRingCat.of k)) J)) ?_ ?_ ?_ I inferInstance
  · intro α β e ih _
    have : Finite α := Finite.of_equiv β e.symm
    obtain ⟨n, hn⟩ := ih this
    exact ⟨n, hn.of_iso (piEquivIso e (fun _ => (Gm _).toGrp))⟩
  · intro _
    exact ⟨0, hasSeries_splitTorus_empty PEmpty⟩
  · intro α _ ih _
    obtain ⟨n, hn⟩ := ih inferInstance
    let N := splitTorus (Spec (CommRingCat.of k)) α
    let B := (Gm (Spec (CommRingCat.of k))).toGrp
    exact ⟨n + 1, (hn.tensor_gm (isSplitTorus_splitTorus α)).of_iso
      ((β_ N B) ≪≫ (piOptionIso (fun _ : Option α => B)).symm)⟩

end SplitSolvable

/-- Split tori have solvable geometric points. -/
theorem IsSplitTorus.isSolvableGroupScheme
    {k : Type u} [Field k] {T : GroupScheme (Spec (CommRingCat.of k))}
    (hT : IsSplitTorus T) : IsSolvableGroupScheme T := by
  unfold IsSolvableGroupScheme
  obtain ⟨I, hI, ⟨e⟩⟩ := hT.baseChange (toAlgebraicClosure k)
  let U := Over.mk (𝟙 (Spec (CommRingCat.of (AlgebraicClosure k))))
  let φ := (isoPointsEquiv e U).trans (splitTorus.pointsEquiv I U)
  exact Group.isSolvable_of_isSolvable_injective (f := φ.toMonoidHom) φ.injective

/-- Every split torus over its ground field is split solvable. -/
theorem IsSplitTorus.isSplitSolvableGroupScheme
    {k : Type u} [Field k] {T : GroupScheme (Spec (CommRingCat.of k))}
    (hT : IsSplitTorus T) : IsSplitSolvableGroupScheme T := by
  refine ⟨hT.smooth, hT.isAffineHom, hT.connectedSpace, hT.isSolvableGroupScheme, ?_⟩
  obtain ⟨I, hI, ⟨e⟩⟩ := hT
  obtain ⟨n, hn⟩ := SplitSolvable.exists_hasSeries_splitTorus (k := k) I
  exact ⟨n, hn.of_iso e.symm⟩

/-- The exact published target, in every universe. -/
theorem splitTorusSplitSolvable : SplitTorusSplitSolvableStatement.{u} :=
  fun _ _ _ hT => hT.isSplitSolvableGroupScheme

end Langlands.GroupScheme
