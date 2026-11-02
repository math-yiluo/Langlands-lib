import Langlands.AlgebraicGeometry.Picard.RigidifiedClassesNoetherianApproximationReductionStatement
import Langlands.AlgebraicGeometry.Picard.RigidifiedCarrierIso
import Langlands.AlgebraicGeometry.Picard.RigidifiedPullbackProofs
import Langlands.AlgebraicGeometry.Modules.PullbackTensorProof

/-! # Proof of the reduction of noetherian approximation of agreement to noetherian models -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.SchemeModule

namespace RigidifiedClassesNoetherianApproximationReduction

section Pullback

variable {S X S' X' S'' X'' : Scheme.{u}} {ε : S ⟶ X} {ε' : S' ⟶ X'} {ε'' : S'' ⟶ X''}

/-- Two successive rigidified pullbacks are isomorphic to the pullback along any given
factorisation of the composite square. -/
def pullbackPullbackIso (f : X' ⟶ X) (g : S' ⟶ S) (f' : X'' ⟶ X') (g' : S'' ⟶ S')
    (comm : ε' ≫ f = g ≫ ε) (comm' : ε'' ≫ f' = g' ≫ ε')
    {F : X'' ⟶ X} {G : S'' ⟶ S} (hF : f' ≫ f = F) (hG : g' ≫ g = G)
    (commF : ε'' ≫ F = G ≫ ε) (L : RigidifiedLineBundle ε) :
    (RigidifiedLineBundle.pullback f' g' comm').obj
        ((RigidifiedLineBundle.pullback f g comm).obj L) ≅
      (RigidifiedLineBundle.pullback F G commF).obj L :=
  (RigidifiedLineBundle.pullbackComp RigidifiedModule.pullbackCoherence f g f' g' comm comm'
      (by rw [hF, hG]; exact commF)).app L ≪≫
    (RigidifiedLineBundle.pullbackCongr hF hG _ _).app L

/-- Rigidified pullback along an isomorphism of schemes over an isomorphism of bases reflects
isomorphism of rigidified line bundles. -/
lemma nonempty_iso_of_pullback (f : X' ⟶ X) [IsIso f] (g : S' ⟶ S) [IsIso g]
    (comm : ε' ≫ f = g ≫ ε) {L M : RigidifiedLineBundle ε}
    (e : (RigidifiedLineBundle.pullback f g comm).obj L ≅
      (RigidifiedLineBundle.pullback f g comm).obj M) : Nonempty (L ≅ M) := by
  have comm' : ε ≫ inv f = inv g ≫ ε' := by
    rw [IsIso.eq_inv_comp, ← Category.assoc, ← comm, Category.assoc, IsIso.hom_inv_id,
      Category.comp_id]
  let Φ : ∀ N : RigidifiedLineBundle ε,
      (RigidifiedLineBundle.pullback (inv f) (inv g) comm').obj
        ((RigidifiedLineBundle.pullback f g comm).obj N) ≅ N := fun N ↦
    pullbackPullbackIso f g (inv f) (inv g) comm comm' (IsIso.inv_hom_id f)
        (IsIso.inv_hom_id g) (by simp) N ≪≫
      (RigidifiedLineBundle.pullbackId RigidifiedModule.pullbackCoherence ε).app N
  exact ⟨(Φ L).symm ≪≫ (RigidifiedLineBundle.pullback (inv f) (inv g) comm').mapIso e ≪≫ Φ M⟩

end Pullback

section Relative

variable {S X : Scheme.{u}} (f : X ⟶ S)

@[reassoc]
lemma relativeSpace_map_fst {T U : Over S} (h : T ⟶ U) :
    (relativeSpace f).map h ≫ pullback.fst U.hom f = pullback.fst T.hom f ≫ h.left :=
  pullback.lift_fst _ _ _

@[reassoc]
lemma relativeSection_fst (ε : S ⟶ X) (section_eq : ε ≫ f = 𝟙 S) (T : Over S) :
    (relativeSection f ε section_eq).app T ≫ pullback.fst T.hom f = 𝟙 T.left :=
  pullback.lift_fst _ _ _

end Relative

section Model

variable {S S₀ : Scheme.{u}}

/-- The total space of `A` mapped to the member of its relative family over the identity. -/
def totalSpaceLift (A : AbelianScheme S) :
    A.X.left ⟶ (relativeSpace A.X.hom).obj (Over.mk (𝟙 S)) :=
  pullback.lift A.X.hom (𝟙 A.X.left) (by simp)

@[reassoc]
lemma totalSpaceLift_fst (A : AbelianScheme S) :
    totalSpaceLift A ≫ pullback.fst (Over.mk (𝟙 S)).hom A.X.hom = A.X.hom :=
  pullback.lift_fst _ _ _

@[reassoc]
lemma totalSpaceLift_snd (A : AbelianScheme S) :
    totalSpaceLift A ≫ pullback.snd (Over.mk (𝟙 S)).hom A.X.hom = 𝟙 A.X.left :=
  pullback.lift_snd _ _ _

lemma totalSpaceLift_comm (A : AbelianScheme S) :
    unitSection A ≫ totalSpaceLift A =
      𝟙 S ≫ (relativeSection A.X.hom (unitSection A) (unitSection_comp A)).app
        (Over.mk (𝟙 S)) := by
  apply pullback.hom_ext
  · rw [Category.assoc, totalSpaceLift_fst, Category.id_comp, relativeSection_fst,
      unitSection_comp]
    rfl
  · rw [Category.assoc, totalSpaceLift_snd, Category.id_comp, relativeSection_snd,
      Category.comp_id]
    exact (Category.id_comp _).symm

lemma snd_comm (A : AbelianScheme S) (T : Over S) :
    (relativeSection A.X.hom (unitSection A) (unitSection_comp A)).app T ≫
        pullback.snd T.hom A.X.hom = T.hom ≫ unitSection A :=
  relativeSection_snd _ _ _ T

/-- Restrict a rigidified family over the identity to the total space. -/
def toTotal (A : AbelianScheme S) (F : RigidifiedFamily A (Over.mk (𝟙 S))) :
    RigidifiedLineBundle (unitSection A) :=
  (RigidifiedLineBundle.pullback (totalSpaceLift A) (𝟙 S) (totalSpaceLift_comm A)).obj F

/-- Spread a rigidified line bundle on the total space to the family over the identity. -/
def ofTotal (A : AbelianScheme S) (M : RigidifiedLineBundle (unitSection A)) :
    RigidifiedFamily A (Over.mk (𝟙 S)) :=
  (RigidifiedLineBundle.pullback (pullback.snd (Over.mk (𝟙 S)).hom A.X.hom) (𝟙 S)
    (snd_comm A (Over.mk (𝟙 S)))).obj M

variable {A : AbelianScheme S} {A₀ : AbelianScheme S₀} {b : S ⟶ S₀}
  {a : A.X.left ⟶ A₀.X.left} (hpb : IsPullback a A.X.hom A₀.X.hom b)
  (hunit : unitSection A ≫ a = b ≫ unitSection A₀)

include hpb in
/-- Pasting the chosen fibre product over `T'` with the model square. -/
lemma isPullback_paste (T' : Over S) :
    IsPullback (pullback.fst T'.hom A.X.hom) (pullback.snd T'.hom A.X.hom ≫ a)
      (T'.hom ≫ b) A₀.X.hom :=
  ((IsPullback.of_hasPullback T'.hom A.X.hom).flip.paste_horiz hpb).flip

/-- The comparison between the members over `T'` of the two relative families. -/
def spaceIso (T' : Over S) :
    (relativeSpace A.X.hom).obj T' ≅ (relativeSpace A₀.X.hom).obj (Over.mk (T'.hom ≫ b)) :=
  (isPullback_paste hpb T').isoPullback

@[reassoc]
lemma spaceIso_hom_fst (T' : Over S) :
    (spaceIso hpb T').hom ≫ pullback.fst (Over.mk (T'.hom ≫ b)).hom A₀.X.hom =
      pullback.fst T'.hom A.X.hom :=
  IsPullback.isoPullback_hom_fst _

@[reassoc]
lemma spaceIso_hom_snd (T' : Over S) :
    (spaceIso hpb T').hom ≫ pullback.snd (Over.mk (T'.hom ≫ b)).hom A₀.X.hom =
      pullback.snd T'.hom A.X.hom ≫ a :=
  IsPullback.isoPullback_hom_snd _

include hunit in
lemma spaceIso_comm (T' : Over S) :
    (relativeSection A.X.hom (unitSection A) (unitSection_comp A)).app T' ≫
        (spaceIso hpb T').hom =
      𝟙 T'.left ≫ (relativeSection A₀.X.hom (unitSection A₀) (unitSection_comp A₀)).app
        (Over.mk (T'.hom ≫ b)) := by
  apply pullback.hom_ext
  · rw [Category.assoc, spaceIso_hom_fst, relativeSection_fst, Category.id_comp,
      relativeSection_fst]
    rfl
  · rw [Category.assoc, spaceIso_hom_snd, ← Category.assoc, relativeSection_snd,
      Category.id_comp, relativeSection_snd, Category.assoc, hunit]
    rfl

include hunit in
/-- The pullback to `T'` of a family over the identity is identified, through the comparison
of relative spaces, with the pullback to `T'` of the spread-out model bundle. -/
lemma nonempty_iso_model (T' : Over S) (h : T' ⟶ Over.mk (𝟙 S))
    (F : RigidifiedFamily A (Over.mk (𝟙 S))) (M₀ : RigidifiedLineBundle (unitSection A₀))
    (e : (LineBundle.pullback a).obj ((RigidifiedLineBundle.forget _).obj M₀) ≅
      (RigidifiedLineBundle.forget _).obj (toTotal A F)) :
    Nonempty ((RigidifiedLineBundle.relativePullback A.X.hom (unitSection A)
        (unitSection_comp A) h).obj F ≅
      (RigidifiedLineBundle.pullback (spaceIso hpb T').hom (𝟙 T'.left)
          (spaceIso_comm hpb hunit T')).obj
        ((RigidifiedLineBundle.relativePullback A₀.X.hom (unitSection A₀)
          (unitSection_comp A₀)
          (Over.homMk (T'.hom ≫ b) : Over.mk (T'.hom ≫ b) ⟶ Over.mk (𝟙 S₀))).obj
          (ofTotal A₀ M₀))) := by
  obtain ⟨e'⟩ := RigidifiedLineBundle.nonempty_iso_of_forget_iso
    Langlands.Scheme.Modules.pullbackTensorComparisonIsIso A.X.hom (unitSection_comp A)
    (L := (RigidifiedLineBundle.pullback a b hunit).obj M₀) (M := toTotal A F) e
  have hh : h.left = T'.hom := by simpa using Over.w h
  have commX : (relativeSection A.X.hom (unitSection A) (unitSection_comp A)).app T' ≫
      (pullback.snd T'.hom A.X.hom ≫ a) = (T'.hom ≫ b) ≫ unitSection A₀ := by
    rw [← Category.assoc, snd_comm, Category.assoc, hunit, Category.assoc]
  have hF : pullback.snd T'.hom A.X.hom ≫ totalSpaceLift A =
      (relativeSpace A.X.hom).map h := by
    apply pullback.hom_ext
    · rw [Category.assoc, totalSpaceLift_fst, relativeSpace_map_fst, hh, pullback.condition]
    · rw [Category.assoc, totalSpaceLift_snd, Category.comp_id, Langlands.AlgebraicGeometry.Picard.relativeSpace_map_snd]
  let h₀ : Over.mk (T'.hom ≫ b) ⟶ Over.mk (𝟙 S₀) := Over.homMk (T'.hom ≫ b)
  have hF₀ : (relativeSpace A₀.X.hom).map h₀ ≫
      pullback.snd (Over.mk (𝟙 S₀)).hom A₀.X.hom =
        pullback.snd (Over.mk (T'.hom ≫ b)).hom A₀.X.hom :=
    Langlands.AlgebraicGeometry.Picard.relativeSpace_map_snd _ _
  have hG₀ : h₀.left ≫ 𝟙 S₀ = T'.hom ≫ b := Category.comp_id _
  refine ⟨(pullbackPullbackIso (totalSpaceLift A) (𝟙 S) (pullback.snd T'.hom A.X.hom) T'.hom
      (totalSpaceLift_comm A) (snd_comm A T') hF (by rw [Category.comp_id, hh]) _ F).symm ≪≫
    (RigidifiedLineBundle.pullback _ _ (snd_comm A T')).mapIso e'.symm ≪≫
    pullbackPullbackIso a b (pullback.snd T'.hom A.X.hom) T'.hom hunit (snd_comm A T') rfl rfl
      commX M₀ ≪≫ ?_⟩
  exact ((RigidifiedLineBundle.pullback (spaceIso hpb T').hom (𝟙 T'.left)
        (spaceIso_comm hpb hunit T')).mapIso
      (pullbackPullbackIso (pullback.snd (Over.mk (𝟙 S₀)).hom A₀.X.hom) (𝟙 S₀)
        ((relativeSpace A₀.X.hom).map h₀) h₀.left
        (snd_comm A₀ (Over.mk (𝟙 S₀))) ((relativeSection A₀.X.hom (unitSection A₀)
          (unitSection_comp A₀)).naturality h₀).symm hF₀ hG₀
        (snd_comm A₀ (Over.mk (T'.hom ≫ b))) M₀) ≪≫
    pullbackPullbackIso (pullback.snd (Over.mk (T'.hom ≫ b)).hom A₀.X.hom) (T'.hom ≫ b)
      (spaceIso hpb T').hom (𝟙 T'.left) (snd_comm A₀ (Over.mk (T'.hom ≫ b)))
      (spaceIso_comm hpb hunit T') (spaceIso_hom_snd hpb T') (Category.id_comp _)
      commX M₀).symm

end Model

end RigidifiedClassesNoetherianApproximationReduction

open RigidifiedClassesNoetherianApproximationReduction in
/-- Noetherian models of abelian schemes over an affine base with two rigidified bundles imply
noetherian approximation of the agreement of two rigidified classes. -/
theorem rigidifiedClassesNoetherianApproximationReduction :
    RigidifiedClassesNoetherianApproximationReductionStatement.{u} := by
  intro model R A q r
  induction q using Quotient.inductionOn with | h F => ?_
  induction r using Quotient.inductionOn with | h G => ?_
  obtain ⟨R₀, hR₀, φ, A₀, a, M₁₀, M₂₀, hpb, hunit, ⟨e₁⟩, ⟨e₂⟩⟩ :=
    model R A (toTotal A F) (toTotal A G)
  refine ⟨R₀, hR₀, φ, A₀, Quotient.mk _ (ofTotal A₀ M₁₀), Quotient.mk _ (ofTotal A₀ M₂₀),
    fun T' h ↦ ?_⟩
  obtain ⟨i₁⟩ := nonempty_iso_model hpb hunit T' h F M₁₀ e₁
  obtain ⟨i₂⟩ := nonempty_iso_model hpb hunit T' h G M₂₀ e₂
  simp only [RigidifiedLineBundle.classesPullback, Quotient.map_mk, Quotient.eq]
  constructor
  · rintro ⟨j⟩
    exact nonempty_iso_of_pullback _ _ _ (i₁.symm ≪≫ j ≪≫ i₂)
  · rintro ⟨j⟩
    exact ⟨i₁ ≪≫ (RigidifiedLineBundle.pullback _ _ _).mapIso j ≪≫ i₂.symm⟩

end Langlands.AbelianScheme
