import Langlands.GroupScheme.Rational.FppfQuotientSmooth
import Langlands.GroupScheme.Rational.SplitTorusFactorization
import Langlands.GroupScheme.CentralIsogeny.Basic
import Langlands.GroupScheme.CentralIsogeny.Transport
import Langlands.AlgebraicGeometry.Morphisms.FpqcFiniteDescent

/-! # Transferring a central product isogeny to the quotient pairing -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {S : Scheme.{u}} {A B G Q P : GroupScheme S}

theorem prodHom_swap
    (a : A ⟶ G) (b : B ⟶ G)
    (hc : ∀ (T : Over S) (x : T ⟶ A.X) (y : T ⟶ B.X),
      Commute (x ≫ a.hom.hom) (y ≫ b.hom.hom)) :
    prodHom b a (fun T y x => (hc T x y).symm) =
      (β_ B A).hom ≫ prodHom a b hc := by
  apply hom_ext_points
  intro T x
  rw [Grp.comp_hom_hom, ← Category.assoc, comp_prodHom, comp_prodHom]
  simp only [productPointsEquiv_fst, productPointsEquiv_snd,
    Grp.braiding_hom_hom_hom, Category.assoc, braiding_hom_fst_assoc,
    braiding_hom_snd_assoc]
  exact (hc T (x ≫ snd B.X A.X) (x ≫ fst B.X A.X)).symm.eq

private theorem whiskerRight_isPullback {X Y Z : Over S} (f : X ⟶ Y) :
    IsPullback (f ▷ Z) (fst X Z) (fst Y Z) f := by
  refine ⟨⟨by simp⟩, ⟨PullbackCone.IsLimit.mk _
    (fun c => lift c.snd (c.fst ≫ snd Y Z)) ?_ ?_ ?_⟩⟩
  · intro c
    apply CartesianMonoidalCategory.hom_ext
    · simpa only [Category.assoc, whiskerRight_fst, lift_fst_assoc] using c.condition.symm
    · simp
  · intro c
    simp
  · intro c m hm hn
    apply CartesianMonoidalCategory.hom_ext
    · simpa using hn
    · simpa using congrArg (fun t => t ≫ snd Y Z) hm

private theorem whiskerLeft_isPullback {X Y Z : Over S} (f : X ⟶ Y) :
    IsPullback (Z ◁ f) (snd Z X) (snd Z Y) f := by
  refine ⟨⟨by simp⟩, ⟨PullbackCone.IsLimit.mk _
    (fun c => lift (c.fst ≫ fst Z Y) c.snd) ?_ ?_ ?_⟩⟩
  · intro c
    apply CartesianMonoidalCategory.hom_ext
    · simp
    · simpa only [Category.assoc, whiskerLeft_snd, lift_snd_assoc] using c.condition.symm
  · intro c
    simp
  · intro c m hm hn
    apply CartesianMonoidalCategory.hom_ext
    · simpa using congrArg (fun t => t ≫ fst Z Y) hm
    · simpa using hn

theorem prodHom_hom_eq_quotientCellMultiplication
    (a : A ⟶ G) (b : B ⟶ G)
    (hc : ∀ (T : Over S) (x : T ⟶ A.X) (y : T ⟶ B.X),
      Commute (x ≫ a.hom.hom) (y ≫ b.hom.hom)) :
    (prodHom a b hc).hom.hom = QuotientCell.multiplication b a.hom.hom := by
  have h := comp_prodHom a b hc (A ⊗ B).X (𝟙 _)
  simpa only [Category.id_comp, productPointsEquiv_fst, productPointsEquiv_snd,
    QuotientCell.multiplication] using h

set_option backward.isDefEq.respectTransparency.types false in
/-- An isogeny multiplication square descends to the restriction to the other factor. -/
theorem finiteFppf_restriction_of_prodHom
    (a : A ⟶ G) (b : B ⟶ G)
    (hc : ∀ (T : Over S) (x : T ⟶ A.X) (y : T ⟶ B.X),
      Commute (x ≫ a.hom.hom) (y ≫ b.hom.hom))
    [Mono b.hom.hom] (q : G ⟶ Q)
    (hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range b) q)
    (hm : IsCentralIsogeny (prodHom a b hc)) :
    IsFinite (a ≫ q).hom.hom.left ∧ Flat (a ≫ q).hom.hom.left ∧
      Surjective (a ≫ q).hom.hom.left ∧
      LocallyOfFinitePresentation (a ≫ q).hom.hom.left := by
  have hb : (SubgroupFunctor.range b).IsRepresentedBy b := ⟨inferInstance, rfl⟩
  have hpb := (QuotientCell.multiplication_isPullback b a.hom.hom q.hom.hom
    (hq.fibers_iff hb)).map (Over.forget S)
  rw [← prodHom_hom_eq_quotientCellMultiplication a b hc] at hpb
  have hcover : (@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation :
      MorphismProperty Scheme.{u}) q.hom.hom.left := ⟨⟨hq.2.1, hq.1⟩, hq.2.2.1⟩
  exact ⟨MorphismProperty.of_isPullback_of_descendsAlong hpb hcover hm.isFinite,
    MorphismProperty.of_isPullback_of_descendsAlong hpb hcover hm.flat,
    MorphismProperty.of_isPullback_of_descendsAlong hpb hcover hm.surjective,
    MorphismProperty.of_isPullback_of_descendsAlong hpb hcover hm.locallyOfFinitePresentation⟩

private theorem quotient_comp_eq_one
    (a : A ⟶ G) (p : G ⟶ P)
    (hp : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range a) p)
    {T : Over S} (x : T ⟶ A.X) :
    (x ≫ a.hom.hom) ≫ p.hom.hom = 1 := by
  apply (mem_range_kernelι_iff p _).mp
  rw [hp.2.2.2]
  exact ⟨x, rfl⟩

/-- Multiplication is the pullback of the quotient pairing along the first restriction
times the identity. -/
theorem quotientPairing_isPullback
    (a : A ⟶ G) (b : B ⟶ G)
    (hc : ∀ (T : Over S) (x : T ⟶ A.X) (y : T ⟶ B.X),
      Commute (x ≫ a.hom.hom) (y ≫ b.hom.hom))
    [Mono b.hom.hom] (q : G ⟶ Q)
    (hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range b) q)
    (p : G ⟶ P)
    (hp : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range a) p) :
    IsPullback (prodHom a b hc).hom.hom
      (A.X ◁ (b ≫ p).hom.hom)
      (lift q p).hom.hom
      ((a ≫ q).hom.hom ▷ P.X) := by
  have hb : (SubgroupFunctor.range b).IsRepresentedBy b := ⟨inferInstance, rfl⟩
  have houter := QuotientCell.multiplication_isPullback b a.hom.hom q.hom.hom
    (hq.fibers_iff hb)
  rw [← prodHom_hom_eq_quotientCellMultiplication a b hc] at houter
  change IsPullback (prodHom a b hc).hom.hom
    (A.X ◁ (b.hom.hom ≫ p.hom.hom)) (lift q.hom.hom p.hom.hom)
    ((a.hom.hom ≫ q.hom.hom) ▷ P.X)
  apply IsPullback.of_bot (v₂₁ := fst A.X P.X) (v₂₂ := fst Q.X P.X)
    ?_ ?_ (whiskerRight_isPullback (a.hom.hom ≫ q.hom.hom))
  · simpa only [whiskerLeft_fst, lift_fst] using houter
  · apply CartesianMonoidalCategory.hom_ext
    · simpa only [Category.assoc, lift_fst, whiskerRight_fst, whiskerLeft_fst_assoc]
        using houter.w
    · simp only [Category.assoc, lift_snd, whiskerRight_snd]
      rw [prodHom_hom_eq_quotientCellMultiplication, QuotientCell.multiplication,
        MonObj.mul_comp, quotient_comp_eq_one a p hp, one_mul]
      simp

/-- A central multiplication isogeny induces a central isogeny to the product of the
two represented fppf quotients. -/
theorem isCentralIsogeny_quotientPairing_of_prodHom
    (a : A ⟶ G) (b : B ⟶ G) (ha : IsCentral a)
    (hc : ∀ (T : Over S) (x : T ⟶ A.X) (y : T ⟶ B.X),
      Commute (x ≫ a.hom.hom) (y ≫ b.hom.hom))
    [Mono a.hom.hom] [Mono b.hom.hom]
    (q : G ⟶ Q)
    (hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range b) q)
    (p : G ⟶ P)
    (hp : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range a) p)
    (hm : IsCentralIsogeny (prodHom a b hc)) :
    IsCentralIsogeny (lift q p) := by
  have hrev : IsCentralIsogeny (prodHom b a (fun T y x => (hc T x y).symm)) := by
    rw [prodHom_swap]
    exact hm.iso_comp (β_ B A)
  have hresA := finiteFppf_restriction_of_prodHom a b hc q hq hm
  have hresB := finiteFppf_restriction_of_prodHom b a
    (fun T y x => (hc T x y).symm) p hp hrev
  have hleft := (whiskerLeft_isPullback (Z := A.X) (b ≫ p).hom.hom).flip.map
    (Over.forget S)
  have hbottom := (whiskerRight_isPullback (Z := P.X) (a ≫ q).hom.hom).flip.map
    (Over.forget S)
  have hbottom_fin : IsFinite ((a ≫ q).hom.hom ▷ P.X).left :=
    MorphismProperty.of_isPullback hbottom hresA.1
  let : IsFinite ((a ≫ q).hom.hom ▷ P.X).left := hbottom_fin
  have hcover : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{u})
      ((a ≫ q).hom.hom ▷ P.X).left :=
    ⟨⟨MorphismProperty.of_isPullback hbottom hresA.2.2.1,
      MorphismProperty.of_isPullback hbottom hresA.2.1⟩, inferInstance⟩
  have hpair := (quotientPairing_isPullback a b hc q hq p hp).flip.map (Over.forget S)
  have hfin : IsFinite (lift q p).hom.hom.left :=
    MorphismProperty.of_isPullback_of_descendsAlong hpair hcover
      (MorphismProperty.of_isPullback hleft hresB.1)
  have hflat : Flat (lift q p).hom.hom.left :=
    MorphismProperty.of_isPullback_of_descendsAlong hpair hcover
      (MorphismProperty.of_isPullback hleft hresB.2.1)
  have hsurj : Surjective (lift q p).hom.hom.left :=
    MorphismProperty.of_isPullback_of_descendsAlong hpair hcover
      (MorphismProperty.of_isPullback hleft hresB.2.2.1)
  have hlfp : LocallyOfFinitePresentation (lift q p).hom.hom.left :=
    MorphismProperty.of_isPullback_of_descendsAlong hpair hcover
      (MorphismProperty.of_isPullback hleft hresB.2.2.2)
  refine ⟨⟨hfin, hflat, hsurj⟩, hlfp, ?_⟩
  apply (isCentral_kernelι_iff _).mpr
  intro T x hx
  change x ≫ lift q.hom.hom p.hom.hom = 1 at hx
  have hxp : x ≫ p.hom.hom = 1 := by
    have h := congrArg (fun t => t ≫ snd Q.X P.X) hx
    simpa only [Category.assoc, lift_snd, MonObj.one_comp] using h
  have hxa : x ∈ (SubgroupFunctor.range a).carrier T := by
    rw [← hp.2.2.2]
    exact (mem_range_kernelι_iff p x).mpr hxp
  obtain ⟨y, rfl⟩ := hxa
  exact ha T y

/-- Internal quotient-pairing reduction over every base scheme. -/
def QuotientPairingTransferStatement : Prop :=
  ∀ (S : Scheme.{u}) (A B G Q P : GroupScheme S)
    (a : A ⟶ G) (b : B ⟶ G) (_ha : IsCentral a)
    (hc : ∀ (T : Over S) (x : T ⟶ A.X) (y : T ⟶ B.X),
      Commute (x ≫ a.hom.hom) (y ≫ b.hom.hom))
    [Mono a.hom.hom] [Mono b.hom.hom]
    (q : G ⟶ Q),
    RelativeRoot.IsFppfQuotient (SubgroupFunctor.range b) q →
    ∀ (p : G ⟶ P),
    RelativeRoot.IsFppfQuotient (SubgroupFunctor.range a) p →
    IsCentralIsogeny (prodHom a b hc) → IsCentralIsogeny (lift q p)

theorem quotientPairingTransfer : QuotientPairingTransferStatement.{u} :=
  @isCentralIsogeny_quotientPairing_of_prodHom

end Langlands.GroupScheme
