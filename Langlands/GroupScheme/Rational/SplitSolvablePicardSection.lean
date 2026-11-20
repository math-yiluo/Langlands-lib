import Langlands.GroupScheme.SplitSolvable
import Langlands.GroupScheme.SplitUnipotentAffineTorsorProof
import Langlands.GroupScheme.SplitUnipotentTorsor.VectorRetract
import Langlands.GroupScheme.Torus.PicardTrivialCocycle
import Langlands.GroupScheme.Torus.Diagonalizable
import Langlands.GroupScheme.Rational.VectorCoordinateGeometry
import Langlands.GroupScheme.VectorGroupQuotient
import Langlands.Algebra.IntLatticeAlgebra

/-! # Sections of split-solvable series quotients over Picard-trivial affine bases

Cocycles of a group with a split-solvable series vanish on affine faithfully flat covers of
affine schemes whose ring of global functions has trivial Picard group. Since the coordinate
rings of `𝔾ₐ` and `𝔾ₘ` have trivial Picard groups, every quotient map in a split-solvable
series has a section as a morphism of schemes.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- A ring isomorphic to a ring with trivial Picard group has trivial Picard group. -/
theorem subsingleton_pic_of_ringEquiv_of_subsingleton {A B : Type u} [CommRing A] [CommRing B]
    (e : A ≃+* B) [Subsingleton (CommRing.Pic B)] : Subsingleton (CommRing.Pic A) := by
  constructor
  intro M N
  have hgf : (e.symm : B →+* A).comp (e : A →+* B) = RingHom.id A := by
    ext x
    simp
  rw [← CommRing.Pic.mapRingHom_id_apply (M := M), ← CommRing.Pic.mapRingHom_id_apply (M := N),
    ← hgf, ← CommRing.Pic.mapRingHom_mapRingHom, ← CommRing.Pic.mapRingHom_mapRingHom,
    Subsingleton.elim (CommRing.Pic.mapRingHom (e : A →+* B) M)
      (CommRing.Pic.mapRingHom (e : A →+* B) N)]

/-- Isomorphic schemes have isomorphic rings of global functions, so triviality of the
Picard group of the global functions transfers along a scheme isomorphism. -/
theorem subsingleton_pic_of_scheme_iso {X Y : Scheme.{u}} (e : X ≅ Y)
    (hY : Subsingleton (CommRing.Pic Γ(Y, ⊤))) : Subsingleton (CommRing.Pic Γ(X, ⊤)) :=
  @subsingleton_pic_of_ringEquiv_of_subsingleton _ _ _ _
    (Scheme.Γ.mapIso e.op).symm.commRingCatIsoToRingEquiv hY

/-- The ring of global functions of an affine spectrum has trivial Picard group when the ring
does. -/
theorem subsingleton_pic_Γ_Spec (A : CommRingCat.{u}) [Subsingleton (CommRing.Pic A)] :
    Subsingleton (CommRing.Pic Γ(Spec A, ⊤)) :=
  subsingleton_pic_of_ringEquiv_of_subsingleton (Scheme.ΓSpecIso A).commRingCatIsoToRingEquiv

namespace Cocycle

variable {S : Scheme.{u}} [IsAffine S] [Subsingleton (CommRing.Pic Γ(S, ⊤))]
  {I : Type u} [Finite I] {U : Over S}
  [IsAffineHom U.hom] [Flat U.hom] [Surjective U.hom]

/-- Split-torus cocycles on affine faithfully flat covers of an affine scheme vanish when the
global functions of the scheme have trivial Picard group. -/
theorem isTrivial_split_of_isAffine_of_pic_trivial (ξ : Cocycle (splitTorus S I) U) :
    ξ.IsTrivial := by
  let p : U.left ⟶ Spec Γ(S, ⊤) := U.hom ≫ S.isoSpec.hom
  have hp : ∀ {Z : Scheme.{u}} (a b : Z ⟶ U.left), a ≫ p = b ≫ p →
      a ≫ U.hom = b ≫ U.hom := by
    intro Z a b h
    have h' := congrArg (· ≫ S.isoSpec.inv) h
    simpa [p] using h'
  let c : I → ∀ (Z : Scheme.{u}) (a b : Z ⟶ U.left), a ≫ p = b ≫ p → Γ(Z, ⊤)ˣ :=
    fun i Z a b h => ξ.unitCoordinate i Z a b (hp a b h)
  have hnat : ∀ i, Langlands.Scheme.UnitCocycleDescent.IsNatural p (c i) :=
    fun i Z Z' t a b h h' =>
      ξ.unitCoordinate_isNatural i Z Z' t a b (hp a b h) (hp _ _ h')
  have hmul : ∀ i, Langlands.Scheme.UnitCocycleDescent.IsMultiplicative p (c i) :=
    fun i Z a b d h h' h'' =>
      ξ.unitCoordinate_isMultiplicative i Z a b d (hp _ _ h) (hp _ _ h') (hp _ _ h'')
  let f : U ⟶ (splitTorus S I).X := (splitTorus.pointsEquiv I U).symm fun i =>
    Langlands.Scheme.Modules.unitCoboundaryOfPicTrivial p (c i) (hnat i) (hmul i)
  refine ⟨f, fun {Z} a b => ?_⟩
  apply (splitTorus.pointsEquiv I Z).injective
  funext i
  have hab : a.left ≫ p = b.left ≫ p := by
    simp only [p, ← Category.assoc, Over.w a, Over.w b]
  have h := Langlands.Scheme.Modules.unitCoboundaryOfPicTrivial_spec p (c i) (hnat i)
    (hmul i) Z.left a.left b.left hab
  change ξ.unitCoordinate i Z.left a.left b.left _ = _ at h
  rw [ξ.unitCoordinate_eq i Z a.left b.left (Over.w a) (Over.w b)] at h
  rw [show (Over.homMk a.left (Over.w a) : Z ⟶ U) = a from by ext; rfl,
    show (Over.homMk b.left (Over.w b) : Z ⟶ U) = b from by ext; rfl] at h
  simpa [splitTorus.pointsEquiv_naturality, f, splitTorus.unitsRestrict] using h

end Cocycle

namespace SplitSolvablePicard

open RelativeRoot SplitUnipotentAffineTorsor

variable {R : CommRingCat.{u}}

/-- Every cocycle of the base change of `H` to an affine scheme over the base whose global
functions have trivial Picard group, on an affine flat surjective cover of that scheme, is
trivial. -/
def PicCocyclesVanish (H : GroupScheme (Spec R)) : Prop :=
  ∀ (T : Over (Spec R)) [IsAffine T.left] [Subsingleton (CommRing.Pic Γ(T.left, ⊤))]
    (U : Over T.left) [IsAffine U.left] [Flat U.hom] [Surjective U.hom]
    (ξ : Cocycle ((GroupScheme.baseChange T.hom).obj H) U), ξ.IsTrivial

/-- Vanishing over all affine bases implies vanishing over Picard-trivial affine bases. -/
theorem PicCocyclesVanish.of_cocyclesVanish {H : GroupScheme (Spec R)}
    (h : CocyclesVanish H) : PicCocyclesVanish H :=
  fun T _ _ U _ _ _ ξ => h T U ξ

/-- One-dimensional vector groups have Picard-trivial cocycle vanishing. -/
theorem picCocyclesVanish_of_isVectorGroup {V : GroupScheme (Spec R)}
    (hV : IsVectorGroupOfDimension V 1) : PicCocyclesVanish V :=
  fun T _ _ U _ _ _ ξ => Cocycle.isTrivial_of_isVectorGroupOfDimension_one hV T U ξ

/-- Split tori have Picard-trivial cocycle vanishing. -/
theorem picCocyclesVanish_of_isSplitTorus {V : GroupScheme (Spec R)}
    (hV : IsSplitTorus V) : PicCocyclesVanish V := by
  intro T _ _ U _ _ _ ξ
  obtain ⟨I, _, ⟨e⟩⟩ := hV
  let φ : (GroupScheme.baseChange T.hom).obj V ≅ splitTorus T.left I :=
    (GroupScheme.baseChange T.hom).mapIso e ≪≫ splitTorus.baseChangeIso T.hom I
  apply Cocycle.IsTrivial.of_map_retract φ.hom φ.inv φ.hom_inv_id
  exact (ξ.map φ.hom).isTrivial_split_of_isAffine_of_pic_trivial

section Step

variable {K H V : GroupScheme (Spec R)} (j : K ⟶ H) (q : H ⟶ V) [Mono j.hom.hom]
  (hjq : SubgroupFunctor.range (kernelι q) = SubgroupFunctor.range j)

include hjq in
/-- A quotient map onto `V` whose kernel has Picard-trivial cocycle vanishing has a section
as a morphism of schemes over the base, when the global functions of `V` have trivial Picard
group. -/
theorem exists_section [IsAffine H.X.left] [IsAffine V.X.left]
    [Subsingleton (CommRing.Pic Γ(V.X.left, ⊤))] [Flat q.hom.hom.left]
    [Surjective q.hom.hom.left]
    (hK : PicCocyclesVanish K) : ∃ σ : V.X ⟶ H.X, σ ≫ q.hom.hom = 𝟙 V.X := by
  let b := V.X.hom
  let U' : Over V.X.left := Over.mk q.hom.hom.left
  have : IsAffine U'.left := ‹IsAffine H.X.left›
  have : Flat U'.hom := ‹Flat q.hom.hom.left›
  have : Surjective U'.hom := ‹Surjective q.hom.hom.left›
  have : EffectiveEpi U'.hom := (inferInstance : EffectiveEpi q.hom.hom.left)
  let e : (Over.map b).obj U' ⟶ H.X :=
    Over.homMk (𝟙 H.X.left) ((Category.id_comp _).trans (Over.w q.hom.hom).symm)
  let F : U' ⟶ ((GroupScheme.baseChange b).obj H).X := (baseChangePointsEquiv b H U').symm e
  let q' := ((GroupScheme.baseChange b).map q).hom.hom
  let j' := ((GroupScheme.baseChange b).map j).hom.hom
  have hFq : ∀ {Z : Over V.X.left} (a₁ a₂ : Z ⟶ U'), a₁ ≫ F ≫ q' = a₂ ≫ F ≫ q' := by
    intro Z a₁ a₂
    apply (baseChangePointsEquiv b V Z).injective
    rw [← Category.assoc, ← Category.assoc, baseChangePointsEquiv_comp,
      baseChangePointsEquiv_comp, baseChangePointsEquiv_naturality,
      baseChangePointsEquiv_naturality, MulEquiv.apply_symm_apply]
    apply Over.OverMorphism.ext
    change a₁.left ≫ 𝟙 _ ≫ q.hom.hom.left = a₂.left ≫ 𝟙 _ ≫ q.hom.hom.left
    exact (Over.w a₁).trans (Over.w a₂).symm
  have hval : ∀ {Z : Over V.X.left} (a₁ a₂ : Z ⟶ U'),
      ∃ k : Z ⟶ ((GroupScheme.baseChange b).obj K).X,
        k ≫ j' = (Cocycle.coboundary F).toFun a₁ a₂ := by
    intro Z a₁ a₂
    refine baseChange_exists_comp_eq b hjq _ ?_
    change ((a₁ ≫ F) * (a₂ ≫ F)⁻¹) ≫ q' = 1
    rw [MonObj.mul_comp, GrpObj.inv_comp, Category.assoc, Category.assoc, hFq a₁ a₂,
      mul_inv_cancel]
  obtain ⟨f₂, hf₂⟩ := hK V.X U' ((Cocycle.coboundary F).lift _ hval)
  let J : U' ⟶ ((GroupScheme.baseChange b).obj H).X := f₂ ≫ j'
  have hJ : ∀ {Z : Over V.X.left} (a₁ a₂ : Z ⟶ U'),
      (a₁ ≫ J) * (a₂ ≫ J)⁻¹ = (a₁ ≫ F) * (a₂ ≫ F)⁻¹ := by
    intro Z a₁ a₂
    have h := Cocycle.lift_toFun _ _ hval a₁ a₂
    rw [hf₂ a₁ a₂, MonObj.mul_comp, GrpObj.inv_comp] at h
    simp only [J, Category.assoc] at h ⊢
    exact h
  obtain ⟨s, hs, hs'⟩ := exists_section_of_forall_eq (J⁻¹ * F) fun {Z} a₁ a₂ => by
    rw [MonObj.comp_mul, MonObj.comp_mul, GrpObj.comp_inv, GrpObj.comp_inv]
    calc (a₁ ≫ J)⁻¹ * (a₁ ≫ F)
        = (a₁ ≫ J)⁻¹ * ((a₁ ≫ F) * (a₂ ≫ F)⁻¹) * (a₂ ≫ F) := by group
      _ = (a₁ ≫ J)⁻¹ * ((a₁ ≫ J) * (a₂ ≫ J)⁻¹) * (a₂ ≫ F) := by rw [hJ]
      _ = (a₂ ≫ J)⁻¹ * (a₂ ≫ F) := by group
  let p : ((GroupScheme.baseChange b).obj H).X.left ⟶ H.X.left := Limits.pullback.fst H.X.hom b
  have hp : p ≫ H.X.hom = ((GroupScheme.baseChange b).obj H).X.hom ≫ b :=
    Limits.pullback.condition
  refine ⟨Over.homMk (s ≫ p) ?_, ?_⟩
  · change (s ≫ p) ≫ H.X.hom = b
    rw [Category.assoc, hp, ← Category.assoc, hs', Category.id_comp]
  · have hFJ : baseChangePointsEquiv b H U' (J⁻¹ * F) ≫ q.hom.hom = e ≫ q.hom.hom := by
      rw [map_mul, map_inv, MulEquiv.apply_symm_apply, MonObj.mul_comp, GrpObj.inv_comp]
      have : baseChangePointsEquiv b H U' J ≫ q.hom.hom = 1 := by
        rw [← baseChangePointsEquiv_comp, Category.assoc,
          baseChange_comp_comp_eq_one b hjq f₂, map_one]
      rw [this, inv_one, one_mul]
    apply Over.OverMorphism.ext
    change (s ≫ p) ≫ q.hom.hom.left = 𝟙 V.X.left
    rw [← cancel_epi U'.hom, ← Category.assoc, ← Category.assoc, hs, Category.comp_id]
    have h := congrArg (fun g => g.left) hFJ
    change ((J⁻¹ * F).left ≫ p) ≫ q.hom.hom.left = 𝟙 H.X.left ≫ q.hom.hom.left at h
    rw [h, Category.id_comp]
    rfl

include hjq in
/-- The induction step: Picard-trivial cocycles of `H` vanish once those of the kernel and
quotient do and the quotient map has a section. -/
theorem picCocyclesVanish_of_section (σ : V.X ⟶ H.X) (hσ : σ ≫ q.hom.hom = 𝟙 V.X)
    (hV : PicCocyclesVanish V) (hK : PicCocyclesVanish K) : PicCocyclesVanish H := by
  intro T _ _ U _ _ _ ξ
  let b := T.hom
  let q' := ((GroupScheme.baseChange b).map q).hom.hom
  obtain ⟨f₀, hf₀⟩ := hV T U (ξ.map ((GroupScheme.baseChange b).map q))
  let f₁ : U ⟶ ((GroupScheme.baseChange b).obj H).X :=
    (baseChangePointsEquiv b H U).symm (baseChangePointsEquiv b V U f₀ ≫ σ)
  have hf₁ : f₁ ≫ q' = f₀ := by
    apply (baseChangePointsEquiv b V U).injective
    rw [baseChangePointsEquiv_comp, MulEquiv.apply_symm_apply, Category.assoc, hσ,
      Category.comp_id]
  have hval : ∀ {Z : Over T.left} (a₁ a₂ : Z ⟶ U),
      ∃ k : Z ⟶ ((GroupScheme.baseChange b).obj K).X,
        k ≫ ((GroupScheme.baseChange b).map j).hom.hom = (ξ.twist f₁).toFun a₁ a₂ := by
    intro Z a₁ a₂
    refine baseChange_exists_comp_eq b hjq _ ?_
    have h : ξ.toFun a₁ a₂ ≫ q' = (a₁ ≫ f₀) * (a₂ ≫ f₀)⁻¹ := hf₀ a₁ a₂
    change ((a₁ ≫ f₁)⁻¹ * ξ.toFun a₁ a₂ * (a₂ ≫ f₁)) ≫ q' = 1
    rw [MonObj.mul_comp, MonObj.mul_comp, GrpObj.inv_comp, Category.assoc, Category.assoc, hf₁,
      h]
    group
  exact Cocycle.IsTrivial.of_twist (Cocycle.IsTrivial.of_lift (hK T U ((ξ.twist f₁).lift _ hval)))

end Step

section Field

variable {k : Type u} [Field k]

/-- The coordinate ring of a one-dimensional vector group over a field has trivial Picard
group. -/
theorem subsingleton_pic_of_isVectorGroup {V : GroupScheme (Spec (CommRingCat.of k))}
    (hV : IsVectorGroupOfDimension V 1) : Subsingleton (CommRing.Pic Γ(V.X.left, ⊤)) := by
  obtain ⟨e, he⟩ := hV
  let f := vectorCoordinatesIso e he
  have : Subsingleton (CommRing.Pic (MvPolynomial (Fin 1) k)) := inferInstance
  have : Subsingleton (CommRing.Pic (CommRingCat.of (MvPolynomial (Fin 1) k))) := this
  have : Subsingleton (CommRing.Pic
      Γ(Spec (CommRingCat.of (MvPolynomial (Fin 1) k)), ⊤)) :=
    subsingleton_pic_Γ_Spec _
  exact subsingleton_pic_of_scheme_iso ((Over.forget _).mapIso ((Grp.forget _).mapIso f)) this

/-- The coordinate ring of a group isomorphic to `𝔾ₘ` over a field has trivial Picard
group. -/
theorem subsingleton_pic_of_iso_gm {V : GroupScheme (Spec (CommRingCat.of k))}
    (e : V ≅ (Gm (Spec (CommRingCat.of k))).toGrp) :
    Subsingleton (CommRing.Pic Γ(V.X.left, ⊤)) := by
  let b : (PUnit.{u + 1} → ℤ) ≃+ (PUnit.{u + 1} → ℤ) := AddEquiv.refl _
  let f : V ≅ (Diagonalizable.groupScheme (CommRingCat.of k) (PUnit.{u + 1} → ℤ)).toGrp :=
    e ≪≫ splitTorus.gmIso _ ≪≫ (Diagonalizable.splitIso (CommRingCat.of k) b).symm
  have : Subsingleton (CommRing.Pic (AddMonoidAlgebra k (PUnit.{u + 1} → ℤ))) :=
    IntLatticeAlgebra.subsingleton_pic k PUnit
  have : Subsingleton (CommRing.Pic
      (CommRingCat.of (AddMonoidAlgebra k (PUnit.{u + 1} → ℤ)))) := this
  have : Subsingleton (CommRing.Pic
      Γ(Spec (CommRingCat.of (AddMonoidAlgebra k (PUnit.{u + 1} → ℤ))), ⊤)) :=
    subsingleton_pic_Γ_Spec _
  exact subsingleton_pic_of_scheme_iso ((Over.forget _).mapIso ((Grp.forget _).mapIso f)) this

/-- An elementary split-solvable quotient has a coordinate ring with trivial Picard group. -/
theorem subsingleton_pic_of_elementary {V : GroupScheme (Spec (CommRingCat.of k))}
    (hV : SplitSolvable.IsElementaryQuotient V) : Subsingleton (CommRing.Pic Γ(V.X.left, ⊤)) := by
  rcases hV with hV | ⟨⟨e⟩⟩
  · exact subsingleton_pic_of_isVectorGroup hV
  · exact subsingleton_pic_of_iso_gm e

/-- An elementary split-solvable quotient is affine over the field. -/
theorem isAffineHom_of_elementary {V : GroupScheme (Spec (CommRingCat.of k))}
    (hV : SplitSolvable.IsElementaryQuotient V) : IsAffineHom V.X.hom := by
  rcases hV with hV | ⟨⟨e⟩⟩
  · exact hV.isAffineHom_overRing
  · exact (IsSplitTorus.of_iso e isSplitTorus_gm).isAffineHom

/-- An elementary split-solvable quotient has Picard-trivial cocycle vanishing. -/
theorem picCocyclesVanish_of_elementary {V : GroupScheme (Spec (CommRingCat.of k))}
    (hV : SplitSolvable.IsElementaryQuotient V) : PicCocyclesVanish V := by
  rcases hV with hV | ⟨⟨e⟩⟩
  · exact picCocyclesVanish_of_isVectorGroup hV
  · exact picCocyclesVanish_of_isSplitTorus (IsSplitTorus.of_iso e isSplitTorus_gm)

/-- A step of a split-solvable series, with a kernel having Picard-trivial cocycle vanishing,
has a section of its quotient map as a morphism of schemes. -/
theorem exists_section_of_step {N H V : GroupScheme (Spec (CommRingCat.of k))}
    (j : N ⟶ H) (q : H ⟶ V) (hj : IsClosedSubgroup j)
    (hq : IsFppfQuotient (SubgroupFunctor.range j) q)
    (hV : SplitSolvable.IsElementaryQuotient V) [IsAffineHom H.X.hom]
    (hN : PicCocyclesVanish N) : ∃ σ : V.X ⟶ H.X, σ ≫ q.hom.hom = 𝟙 V.X := by
  have : IsClosedImmersion j.hom.hom.left := hj
  have : Mono j.hom.hom := Over.mono_of_mono_left _
  have : IsAffine H.X.left := isAffine_of_isAffineHom H.X.hom
  have : IsAffineHom V.X.hom := isAffineHom_of_elementary hV
  have : IsAffine V.X.left := isAffine_of_isAffineHom V.X.hom
  have : Subsingleton (CommRing.Pic Γ(V.X.left, ⊤)) := subsingleton_pic_of_elementary hV
  have : Flat q.hom.hom.left := hq.1
  have : Surjective q.hom.hom.left := hq.2.1
  exact exists_section j q hq.2.2.2 hN

/-- Picard-trivial cocycle vanishing for affine groups with a split-solvable series. -/
theorem picCocyclesVanish_of_hasSeries :
    ∀ (n : ℕ) (H : GroupScheme (Spec (CommRingCat.of k))), SplitSolvable.HasSeries n H →
      IsAffineHom H.X.hom → PicCocyclesVanish H
  | 0, _, h, _ => PicCocyclesVanish.of_cocyclesVanish (cocyclesVanish_of_range_id_eq_bot h)
  | n + 1, H, ⟨N, V, j, q, hj, _, _, _, hq, hV, hN⟩, _ => by
    have : IsClosedImmersion j.hom.hom.left := hj
    have : Mono j.hom.hom := Over.mono_of_mono_left _
    have hNa : IsAffineHom N.X.hom := by
      rw [← Over.w j.hom.hom]
      infer_instance
    have hNv := picCocyclesVanish_of_hasSeries n N hN hNa
    obtain ⟨σ, hσ⟩ := exists_section_of_step j q hj hq hV hNv
    exact picCocyclesVanish_of_section j q hq.2.2.2 σ hσ (picCocyclesVanish_of_elementary hV) hNv

/-- Every quotient map in a split-solvable series has a section as a morphism of schemes. -/
theorem exists_section_of_hasSeries {n : ℕ} {N H V : GroupScheme (Spec (CommRingCat.of k))}
    (j : N ⟶ H) (q : H ⟶ V) (hj : IsClosedSubgroup j)
    (hq : IsFppfQuotient (SubgroupFunctor.range j) q)
    (hV : SplitSolvable.IsElementaryQuotient V) [IsAffineHom H.X.hom]
    (hN : SplitSolvable.HasSeries n N) : ∃ σ : V.X ⟶ H.X, σ ≫ q.hom.hom = 𝟙 V.X := by
  have : IsClosedImmersion j.hom.hom.left := hj
  have hNa : IsAffineHom N.X.hom := by
    rw [← Over.w j.hom.hom]
    infer_instance
  exact exists_section_of_step j q hj hq hV (picCocyclesVanish_of_hasSeries n N hN hNa)

end Field

end SplitSolvablePicard

end Langlands.GroupScheme
