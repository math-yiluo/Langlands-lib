import Langlands.AlgebraicGeometry.ProjectiveSpace
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme
import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-! # The twisting sheaves `𝒪(d)` on `Proj` and `𝒪(1)` on projective space

For an `ℕ`-graded ring `A` and `d : ℕ`, the sheaf `S(d)~` on `Proj A` is built as the sheaf of
dependent functions into the localizations `A_𝔭` which are locally fractions `a / b` with `b`
homogeneous of some degree `i`, nonvanishing, and `a` homogeneous of degree `i + d`.
This mirrors Mathlib's construction of the structure sheaf of `Proj`. -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Opposite TopologicalSpace TopCat AlgebraicGeometry

namespace Langlands.AlgebraicGeometry

universe u

namespace ProjTwist

variable {A σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- The localization `A_𝔭` of the ambient ring at the homogeneous prime of a point. -/
abbrev Localizations (x : ProjectiveSpectrum 𝒜) : Type _ :=
  Localization.AtPrime x.asHomogeneousIdeal.toIdeal

variable {𝒜} in
/-- A dependent function on `U` is the fixed fraction `a / b`, with `b` homogeneous of some
degree `i` and nonvanishing on `U`, and `a` homogeneous of degree `i + d`. -/
def IsFraction (d : ℕ) {U : Opens (ProjectiveSpectrum.top 𝒜)}
    (f : ∀ x : U, Localizations 𝒜 x.1) : Prop :=
  ∃ (i : ℕ) (a : 𝒜 (i + d)) (b : 𝒜 i) (hb : ∀ x : U, (b : A) ∉ x.1.asHomogeneousIdeal),
    ∀ x : U, f x = Localization.mk (a : A) ⟨b, hb x⟩

/-- Being a degree-`d` fraction is preserved by restriction. -/
def isFractionPrelocal (d : ℕ) :
    PrelocalPredicate fun x : ProjectiveSpectrum.top 𝒜 => Localizations 𝒜 x where
  pred f := IsFraction d f
  res := by rintro V U i f ⟨j, a, b, hb, w⟩; exact ⟨j, a, b, (hb <| i ·), (w <| i ·)⟩

/-- The local predicate cutting out the sections of `S(d)~`. -/
def isLocallyFraction (d : ℕ) :
    LocalPredicate fun x : ProjectiveSpectrum.top 𝒜 => Localizations 𝒜 x :=
  (isFractionPrelocal 𝒜 d).sheafify

omit [CommRing A] [AddSubgroupClass σ A] [GradedRing 𝒜] in
private lemma mem_of_eq {k l : ℕ} (h : k = l) {a : A} (ha : a ∈ 𝒜 k) : a ∈ 𝒜 l :=
  h ▸ ha

/-- The sections of `S(d)~` over an open set form an additive subgroup. -/
def sectionsAddSubgroup (d : ℕ) (U : Opens (ProjectiveSpectrum.top 𝒜)) :
    AddSubgroup (∀ x : U, Localizations 𝒜 x.1) where
  carrier := {f | (isLocallyFraction 𝒜 d).pred f}
  zero_mem' x := ⟨U, x.2, 𝟙 U, 0, ⟨0, zero_mem _⟩, ⟨1, SetLike.GradedOne.one_mem⟩,
    fun y => y.1.isPrime.one_notMem, fun y => by simp [Localization.mk_zero]⟩
  add_mem' {f g} hf hg x := by
    obtain ⟨Vf, mf, if', jf, ⟨af, haf⟩, ⟨bf, hbf⟩, nf, wf⟩ := hf x
    obtain ⟨Vg, mg, ig, jg, ⟨ag, hag⟩, ⟨bg, hbg⟩, ng, wg⟩ := hg x
    refine ⟨Vf ⊓ Vg, ⟨mf, mg⟩, Opens.infLELeft _ _ ≫ if', jf + jg,
      ⟨bg * af + bf * ag, add_mem (mem_of_eq 𝒜 (by omega) (SetLike.mul_mem_graded hbg haf))
        (mem_of_eq 𝒜 (by omega) (SetLike.mul_mem_graded hbf hag))⟩,
      ⟨bf * bg, SetLike.mul_mem_graded hbf hbg⟩,
      fun y => y.1.asHomogeneousIdeal.toIdeal.primeCompl.mul_mem (nf ⟨y.1, y.2.1⟩)
        (ng ⟨y.1, y.2.2⟩), fun y => ?_⟩
    have ef := wf ⟨y.1, y.2.1⟩
    have eg := wg ⟨y.1, y.2.2⟩
    simp only [Pi.add_apply]
    refine (congrArg₂ (· + ·) ef eg).trans ?_
    rw [Localization.add_mk]
    congr 1
    ring
  neg_mem' {f} hf x := by
    obtain ⟨V, m, i, j, ⟨a, ha⟩, ⟨b, hb⟩, nb, w⟩ := hf x
    exact ⟨V, m, i, j, ⟨-a, neg_mem ha⟩, ⟨b, hb⟩, nb, fun y => by
      simp only [Pi.neg_apply, w y, Localization.neg_mk]⟩

/-- The `Type`-valued sheaf `S(d)~`: the subsheaf of dependent functions cut out by
`isLocallyFraction`. -/
def sectionsInType (d : ℕ) : Sheaf (Type _) (ProjectiveSpectrum.top 𝒜) :=
  subsheafToTypes (isLocallyFraction 𝒜 d)

instance (d : ℕ) (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ) :
    AddCommGroup ((sectionsInType 𝒜 d).1.obj U) :=
  (sectionsAddSubgroup 𝒜 d U.unop).toAddCommGroup

variable {𝒜} in
@[simp]
lemma sectionsInType_add_apply {d : ℕ} {U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ}
    (s t : (sectionsInType 𝒜 d).1.obj U) (x : U.unop) : (s + t).1 x = s.1 x + t.1 x :=
  rfl

variable {𝒜} in
@[simp]
lemma sectionsInType_zero_apply {d : ℕ} {U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ}
    (x : U.unop) : (0 : (sectionsInType 𝒜 d).1.obj U).1 x = 0 :=
  rfl

/-- A section of the structure sheaf times a section of `S(d)~` is again a section of `S(d)~`. -/
lemma smul_mem (d : ℕ) (U : Opens (ProjectiveSpectrum.top 𝒜))
    (r : (ProjectiveSpectrum.Proj.structureSheaf 𝒜).1.obj (op U))
    (f : ∀ x : U, Localizations 𝒜 x.1) (hf : (isLocallyFraction 𝒜 d).pred f) :
    (isLocallyFraction 𝒜 d).pred (fun x => (r.1 x).val * f x) := fun x => by
  obtain ⟨Vr, mr, ir, k, ⟨c, hc⟩, ⟨e, he⟩, ne, wr⟩ := r.2 x
  obtain ⟨Vf, mf, if', j, ⟨a, ha⟩, ⟨b, hb⟩, nb, wf⟩ := hf x
  refine ⟨Vr ⊓ Vf, ⟨mr, mf⟩, Opens.infLELeft _ _ ≫ ir, k + j,
    ⟨c * a, mem_of_eq 𝒜 (by omega) (SetLike.mul_mem_graded hc ha)⟩,
    ⟨e * b, SetLike.mul_mem_graded he hb⟩,
    fun y => y.1.asHomogeneousIdeal.toIdeal.primeCompl.mul_mem (ne ⟨y.1, y.2.1⟩)
      (nb ⟨y.1, y.2.2⟩), fun y => ?_⟩
  have er := wr ⟨y.1, y.2.1⟩
  have ef := wf ⟨y.1, y.2.2⟩
  dsimp only at er ef
  refine (congrArg₂ (fun u v => HomogeneousLocalization.val u * v) er ef).trans ?_
  rw [HomogeneousLocalization.val_mk, Localization.mk_mul]
  rfl

instance (d : ℕ) (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ) :
    SMul ((ProjectiveSpectrum.Proj.structureSheaf 𝒜).1.obj U)
      ((sectionsInType 𝒜 d).1.obj U) where
  smul r s := ⟨fun x => (r.1 x).val * s.1 x, smul_mem 𝒜 d U.unop r s.1 s.2⟩

variable {𝒜} in
@[simp]
lemma sectionsInType_smul_apply {d : ℕ} {U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ}
    (r : (ProjectiveSpectrum.Proj.structureSheaf 𝒜).1.obj U)
    (s : (sectionsInType 𝒜 d).1.obj U) (x : U.unop) : (r • s).1 x = (r.1 x).val * s.1 x :=
  rfl

instance (d : ℕ) (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ) :
    Module ((ProjectiveSpectrum.Proj.structureSheaf 𝒜).1.obj U)
      ((sectionsInType 𝒜 d).1.obj U) where
  one_smul s := Subtype.ext <| funext fun x => by
    simp [HomogeneousLocalization.val_one]
  mul_smul r t s := Subtype.ext <| funext fun x => by
    simp [HomogeneousLocalization.val_mul, mul_assoc]
  smul_zero r := Subtype.ext <| funext fun x => by simp
  smul_add r s t := Subtype.ext <| funext fun x => by simp [mul_add]
  add_smul r t s := Subtype.ext <| funext fun x => by
    simp [HomogeneousLocalization.val_add, add_mul]
  zero_smul s := Subtype.ext <| funext fun x => by
    simp [HomogeneousLocalization.val_zero]

/-- The abelian-group-valued presheaf underlying `S(d)~`. -/
def presheafInAb (d : ℕ) : Presheaf AddCommGrpCat (ProjectiveSpectrum.top 𝒜) where
  obj U := AddCommGrpCat.of ((sectionsInType 𝒜 d).1.obj U)
  map i := AddCommGrpCat.ofHom
    { toFun := (sectionsInType 𝒜 d).1.map i
      map_zero' := rfl
      map_add' := fun _ _ => rfl }

/-- `S(d)~` as a presheaf of modules over the structure sheaf of `Proj`. -/
def presheafOfModules (d : ℕ) : PresheafOfModules (Proj 𝒜).ringCatSheaf.obj :=
  letI (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ) :
      Module ((Proj 𝒜).ringCatSheaf.obj.obj U) ((presheafInAb 𝒜 d).obj U) :=
    inferInstanceAs (Module ((ProjectiveSpectrum.Proj.structureSheaf 𝒜).1.obj U)
      ((sectionsInType 𝒜 d).1.obj U))
  .ofPresheaf (presheafInAb 𝒜 d) fun _ _ _ _ _ => rfl

end ProjTwist

variable {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- The `d`-th twist `𝒪(d) = S(d)~` of the structure sheaf of `Proj 𝒜`, for `d : ℕ`
(Stacks, Definition 27.10.1). -/
def projTwistingSheaf (d : ℕ) : (Proj 𝒜).Modules where
  val := ProjTwist.presheafOfModules 𝒜 d
  isSheaf := (TopCat.Presheaf.isSheaf_iff_isSheaf_comp (forget AddCommGrpCat) _).2
    (ProjTwist.sectionsInType 𝒜 d).2

/-- The global section `a / 1` of `𝒪(d)` defined by a homogeneous element `a` of degree `d`
(the map of Stacks, Equation 27.10.1.3, in degree `d`). -/
def projTwistingSheafSection (d : ℕ) (a : A) (ha : a ∈ 𝒜 d) :
    Γ(projTwistingSheaf 𝒜 d, ⊤) :=
  ⟨fun _ => Localization.mk a 1, fun x => ⟨⊤, x.2, 𝟙 _, 0,
    ⟨a, ProjTwist.mem_of_eq 𝒜 (zero_add d).symm ha⟩, ⟨1, SetLike.GradedOne.one_mem⟩,
    fun y => y.1.isPrime.one_notMem, fun _ => rfl⟩⟩

@[simp]
lemma projTwistingSheafSection_apply (d : ℕ) (a : A) (ha : a ∈ 𝒜 d) (x : (⊤ : (Proj 𝒜).Opens)) :
    (projTwistingSheafSection 𝒜 d a ha).1 x = Localization.mk a 1 :=
  rfl

/-- On `D₊(f)`, for `f` and `a` homogeneous of the same degree `d`, the section `a / 1` of
`𝒪(d)` is the structure-sheaf section `a / f` times the section `f / 1`. -/
lemma projTwistingSheafSection_restrict_basicOpen (d : ℕ) {f a : A} (hf : f ∈ 𝒜 d)
    (ha : a ∈ 𝒜 d) :
    (projTwistingSheaf 𝒜 d).presheaf.map (homOfLE le_top : Proj.basicOpen 𝒜 f ⟶ ⊤).op
        (projTwistingSheafSection 𝒜 d a ha) =
      (Proj.awayToSection 𝒜 f).hom
          (HomogeneousLocalization.Away.mk 𝒜 hf 1 a (by rwa [one_smul])) •
        (projTwistingSheaf 𝒜 d).presheaf.map (homOfLE le_top : Proj.basicOpen 𝒜 f ⟶ ⊤).op
          (projTwistingSheafSection 𝒜 d f hf) := by
  apply Subtype.ext
  funext x
  change Localization.mk a 1 = Localization.mk a ⟨f ^ 1, _⟩ * Localization.mk f 1
  rw [Localization.mk_mul, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  exact ⟨1, by simp only [Submonoid.coe_mul, OneMemClass.coe_one, pow_one]; ring⟩

/-- The degree-one twist `𝒪(1) = S(1)~` on polynomial projective space. -/
def twistOne (R : Type u) [CommRing R] (n : ℕ) : (ProjectiveSpace R n).Modules :=
  projTwistingSheaf (projectiveSpaceGrading R n) 1

/-- The homogeneous coordinate `X i` as a global section of `𝒪(1)` on projective space. -/
def twistOneCoordinate (R : Type u) [CommRing R] (n : ℕ) (i : Fin (n + 1)) :
    Γ(twistOne R n, ⊤) :=
  projTwistingSheafSection (projectiveSpaceGrading R n) 1 (MvPolynomial.X i)
    (projectiveSpace_X_mem R n i)

/-- The ratio `X j / X i`, a section of the structure sheaf over the coordinate open
`D₊(X i)`, given by the degree-zero fraction `X j / X i` of the localization away from `X i`. -/
def projectiveSpaceCoordinateRatio (R : Type u) [CommRing R] (n : ℕ) (i j : Fin (n + 1)) :
    Γ(ProjectiveSpace R n, projectiveSpaceCoordinateOpen R n i) :=
  (Proj.awayToSection (projectiveSpaceGrading R n) (MvPolynomial.X i)).hom
    (HomogeneousLocalization.Away.mk _ (projectiveSpace_X_mem R n i) 1 (MvPolynomial.X j)
      (by rw [one_smul]; exact projectiveSpace_X_mem R n j))

/-- On the coordinate open `D₊(X i)`, the coordinate section `X j` of `𝒪(1)` equals
`X j / X i` times the coordinate section `X i`. -/
lemma twistOneCoordinate_restrict_coordinateOpen (R : Type u) [CommRing R] (n : ℕ)
    (i j : Fin (n + 1)) :
    (twistOne R n).presheaf.map (homOfLE le_top : projectiveSpaceCoordinateOpen R n i ⟶ ⊤).op
        (twistOneCoordinate R n j) =
      projectiveSpaceCoordinateRatio R n i j •
        (twistOne R n).presheaf.map
          (homOfLE le_top : projectiveSpaceCoordinateOpen R n i ⟶ ⊤).op
          (twistOneCoordinate R n i) :=
  projTwistingSheafSection_restrict_basicOpen _ 1 (projectiveSpace_X_mem R n i)
    (projectiveSpace_X_mem R n j)

end Langlands.AlgebraicGeometry
