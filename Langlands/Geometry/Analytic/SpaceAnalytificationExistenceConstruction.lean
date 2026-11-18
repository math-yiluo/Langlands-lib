import Langlands.Geometry.Analytic.SpaceAnalytificationExistenceAffineModels
import Langlands.Geometry.Analytic.EtaleCoverGluing
import Langlands.Geometry.Analytic.LocalizedEtaleComposition
import Langlands.Geometry.Analytic.EtaleGeometricPointPullbacks

/-! # Conditional construction of the point family of an analytification

From a family of étale affine charts of a separated algebraic space `X` that covers every
affine test point, an analytic quotient of the analytified charts, and explicit analytic
inputs, this module constructs the maps `Spec(A)ᵃⁿ → Y` attached to all affine test points
by étale gluing and proves naturality, étaleness for étale points and joint surjectivity.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry

namespace Langlands.Analytic.SpaceAnalytification.ExistenceReduction

open SaturatedAtlasPresentation AffineAnalytification
open Langlands.AlgebraicGeometry Langlands.AlgebraicGeometry.AlgebraicSpace
open Langlands.AlgebraicGeometry.PointTopology

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

variable (K) in
/-- The analytic inputs of the conditional existence argument, specialised to `K`. -/
structure AnalyticInputs : Prop where
  /-- Morphisms to any analytic space form a sheaf on the étale site. -/
  sheaf : ∀ S T : LocalizedCategory.{u, u, u} (K := K),
    Presieve.IsSheaf (etaleTopology S) (etaleHomPresheaf S T)
  /-- Étaleness descends along jointly surjective étale families. -/
  descent : ∀ (S T : LocalizedCategory.{u, u, u} (K := K)) (F : S ⟶ T)
    (J : Type u) (U : J → LocalizedCategory.{u, u, u} (K := K)) (q : ∀ j, U j ⟶ S),
    (∀ j, etale (q j)) →
    (∀ s : localizedSpaceFunctor.obj S,
      ∃ j, s ∈ Set.range (localizedSpaceFunctor.map (q j))) →
    (∀ j, etale (q j ≫ F)) → etale F
  /-- Affine analytification is functorial on compositions. -/
  comp : ∀ {A B C : Type u} [CommRing A] [Algebra K A] [CommRing B] [Algebra K B]
    [CommRing C] [Algebra K C]
    (P : FinitePolynomialPresentation K A) (Q : FinitePolynomialPresentation K B)
    (R : FinitePolynomialPresentation K C) (f : A →ₐ[K] B) (g : B →ₐ[K] C),
    localizedHom K P R (g.comp f) = localizedHom K Q R g ≫ localizedHom K P Q f
  /-- Affine analytification preserves identities. -/
  id : ∀ {A : Type u} [CommRing A] [Algebra K A] (P : FinitePolynomialPresentation K A),
    localizedHom K P P (AlgHom.id K A) = 𝟙 _
  /-- Affine analytification carries presheaf fibre squares of affine tests to pullbacks. -/
  affPullback : ∀ {A B C D : Type u} [CommRing A] [Algebra K A] [CommRing B] [Algebra K B]
    [CommRing C] [Algebra K C] [CommRing D] [Algebra K D]
    (P : FinitePolynomialPresentation K A) (Q : FinitePolynomialPresentation K B)
    (R : FinitePolynomialPresentation K C) (U : FinitePolynomialPresentation K D)
    (f : C →ₐ[K] A) (g : C →ₐ[K] B) (a : A →ₐ[K] D) (b : B →ₐ[K] D),
    IsPullback (ty a) (ty b) (ty f) (ty g) →
    IsPullback (localizedHom K P U a) (localizedHom K Q U b)
      (localizedHom K R P f) (localizedHom K R Q g)
  /-- Affine analytification preserves étale maps. -/
  etaleFwd : ∀ {A B : Type u} [CommRing A] [Algebra K A] [CommRing B] [Algebra K B]
    (P : FinitePolynomialPresentation K A) (Q : FinitePolynomialPresentation K B)
    (f : A →ₐ[K] B), f.toRingHom.Etale → etale (localizedHom K P Q f)
  /-- Pullbacks along étale maps exist and have étale base change. -/
  base : LocalizedEtalePullbackStatement.{u, u} K
  /-- Points of a pullback square with an étale leg lift matching pairs of points. -/
  points : ∀ {W A B C : LocalizedCategory.{u, u, u} (K := K)}
    (p : W ⟶ A) (q : W ⟶ B) (f : A ⟶ C) (g : B ⟶ C), IsPullback p q f g → etale f →
    ∀ (a : localizedSpaceFunctor.obj A) (b : localizedSpaceFunctor.obj B),
      localizedSpaceFunctor.map f a = localizedSpaceFunctor.map g b →
      ∃ z : localizedSpaceFunctor.obj W,
        localizedSpaceFunctor.map p z = a ∧ localizedSpaceFunctor.map q z = b
  /-- Affine analytification carries families jointly surjective on spectra to families
  jointly surjective on points. -/
  surj : ∀ {A : Type u} [CommRing A] [Algebra K A] (P : FinitePolynomialPresentation K A)
    {J : Type u} (B : J → CommAlgCat.{u} K) (Q : ∀ j, FinitePolynomialPresentation K (B j))
    (f : ∀ j, A →ₐ[K] B j),
    (∀ 𝔭 : PrimeSpectrum A, ∃ j, ∃ 𝔮 : PrimeSpectrum (B j),
      PrimeSpectrum.comap (f j).toRingHom 𝔮 = 𝔭) →
    ∀ z : localizedSpaceFunctor.obj (localized K P),
      ∃ j, z ∈ Set.range (localizedSpaceFunctor.map (localizedHom K P (Q j) (f j)))

theorem AnalyticInputs.comp_assoc (H : AnalyticInputs K) {A B C : Type u} [CommRing A]
    [Algebra K A] [CommRing B] [Algebra K B] [CommRing C] [Algebra K C]
    (P : FinitePolynomialPresentation K A) (Q : FinitePolynomialPresentation K B)
    (R : FinitePolynomialPresentation K C) (f : A →ₐ[K] B) (g : B →ₐ[K] C)
    {T : LocalizedCategory.{u, u, u} (K := K)} (h : localized K P ⟶ T) :
    localizedHom K Q R g ≫ localizedHom K P Q f ≫ h = localizedHom K P R (g.comp f) ≫ h := by
  rw [← Category.assoc, H.comp]

/-- A family of étale affine charts of `X` covering every affine test point: for every
point `y` of `X` with values in `B` and every prime of `B`, some chart has the property that
every model of `Spec B ×_X Spec Aᵢ` has a prime over it. -/
structure ChartData (X : AlgebraicSpace (Spec (CommRingCat.of K))) where
  /-- The index type of the charts. -/
  ι : Type u
  /-- The chart algebras. -/
  A : ι → CommAlgCat.{u} K
  /-- Finite polynomial presentations of the chart algebras. -/
  P : ∀ i, FinitePolynomialPresentation K (A i)
  /-- The chart points. -/
  x : ∀ i, RingPoints K X (A i)
  etale : ∀ i, AlgebraicSpace.IsEtale (pointHom K (x i))
  cover : ∀ {B : Type u} [CommRing B] [Algebra K B] (y : RingPoints K X B)
    (𝔭 : PrimeSpectrum B), ∃ i, ∀ M : TestModel (pointHom K y) (pointHom K (x i)),
      ∃ 𝔮 : PrimeSpectrum M.C, PrimeSpectrum.comap M.f.toRingHom 𝔮 = 𝔭

/-- An analytic quotient of the analytified charts: étale, jointly surjective maps to `Y`
carrying the fibre squares of charts to pullback squares. -/
structure QuotientData {X : AlgebraicSpace (Spec (CommRingCat.of K))} (D : ChartData X) where
  /-- The quotient space. -/
  Y : LocalizedCategory.{u, u, u} (K := K)
  /-- The quotient maps. -/
  π : ∀ i, localized K (D.P i) ⟶ Y
  etale : ∀ i, SaturatedAtlasPresentation.etale (π i)
  surj : ∀ y : localizedSpaceFunctor.obj Y,
    ∃ i, y ∈ Set.range (localizedSpaceFunctor.map (π i))
  pullback : ∀ (i j : D.ι) {B : Type u} [CommRing B] [Algebra K B]
    (Q : FinitePolynomialPresentation K B) (f : D.A i →ₐ[K] B) (g : D.A j →ₐ[K] B),
    IsPullback (ty f) (ty g) (pointHom K (D.x i)) (pointHom K (D.x j)) →
      IsPullback (localizedHom K (D.P i) Q f) (localizedHom K (D.P j) Q g) (π i) (π j)

variable {X : AlgebraicSpace (Spec (CommRingCat.of K))} (H : AnalyticInputs K)
  (hX : IsSeparated X) {D : ChartData X} (E : QuotientData D)

include H hX in
/-- Maps of chart analytifications agree on test algebras identified in `X`. -/
theorem chart_compat {Z : Type u} [CommRing Z] [Algebra K Z]
    (R : FinitePolynomialPresentation K Z) (i j : D.ι) (α : D.A i →ₐ[K] Z)
    (β : D.A j →ₐ[K] Z) (h : ty α ≫ pointHom K (D.x i) = ty β ≫ pointHom K (D.x j)) :
    localizedHom K (D.P i) R α ≫ E.π i = localizedHom K (D.P j) R β ≫ E.π j := by
  let M := pointModel hX (D.P i) (D.P j) (D.x i) (D.x j)
  obtain ⟨k, hk₁, hk₂⟩ := M.exists_lift α β h
  have hpb := E.pullback i j M.R M.f M.g M.isPullback
  rw [← hk₁, ← hk₂, H.comp, H.comp, Category.assoc, Category.assoc, hpb.w]

section Cover

variable {B : Type u} [CommRing B] [Algebra K B] (Q : FinitePolynomialPresentation K B)
  (y : RingPoints K X B)

variable (D) in
/-- The chosen model of `Spec B ×_X Spec Aⱼ`. -/
abbrev coverModel (j : D.ι) : TestModel (pointHom K y) (pointHom K (D.x j)) :=
  pointModel hX Q (D.P j) y (D.x j)

variable (D) in
/-- The étale cover maps `(Spec B ×_X Spec Aⱼ)ᵃⁿ → Spec(B)ᵃⁿ`. -/
abbrev coverMap (j : D.ι) :
    localized K (coverModel hX D Q y j).R ⟶ localized K Q :=
  localizedHom K Q (coverModel hX D Q y j).R (coverModel hX D Q y j).f

variable (D) in
include H in
theorem coverMap_etale (j : D.ι) : etale (coverMap hX D Q y j) :=
  H.etaleFwd _ _ _ ((coverModel hX D Q y j).etale_f (D.etale j))

variable (D) in
include H in
theorem coverMap_surj (z : localizedSpaceFunctor.obj (localized K Q)) :
    ∃ j, z ∈ Set.range (localizedSpaceFunctor.map (coverMap hX D Q y j)) := by
  refine H.surj Q (fun j => (coverModel hX D Q y j).C) (fun j => (coverModel hX D Q y j).R)
    (fun j => (coverModel hX D Q y j).f) ?_ z
  intro 𝔭
  obtain ⟨i, hi⟩ := D.cover y 𝔭
  exact ⟨i, hi _⟩

variable (D) in
include H in
/-- Maps out of `Spec(B)ᵃⁿ` agreeing on the cover are equal. -/
theorem ext_of_cover {T : LocalizedCategory.{u, u, u} (K := K)} (g₁ g₂ : localized K Q ⟶ T)
    (h : ∀ j, coverMap hX D Q y j ≫ g₁ = coverMap hX D Q y j ≫ g₂) : g₁ = g₂ :=
  hom_ext_of_etale_cover (H.sheaf _ _) _ (coverMap hX D Q y) (coverMap_etale H hX D Q y)
    (coverMap_surj H hX D Q y) g₁ g₂ h

/-- The maps `(Spec B ×_X Spec Aⱼ)ᵃⁿ → Spec(Aⱼ)ᵃⁿ → Y` to be glued. -/
abbrev coverValue (j : D.ι) : localized K (coverModel hX D Q y j).R ⟶ E.Y :=
  localizedHom K (D.P j) (coverModel hX D Q y j).R (coverModel hX D Q y j).g ≫ E.π j

include H in
theorem coverValue_compat (V : LocalizedCategory.{u, u, u} (K := K)) (j k : D.ι)
    (a : V ⟶ localized K (coverModel hX D Q y j).R)
    (b : V ⟶ localized K (coverModel hX D Q y k).R)
    (hab : a ≫ coverMap hX D Q y j = b ≫ coverMap hX D Q y k) :
    a ≫ coverValue hX E Q y j = b ≫ coverValue hX E Q y k := by
  let Nj := coverModel hX D Q y j
  let Nk := coverModel hX D Q y k
  let G := testModel Nj.R Nk.R Nj.f Nk.f
  have hG : IsPullback (localizedHom K Nj.R G.R G.f) (localizedHom K Nk.R G.R G.g)
      (localizedHom K Q Nj.R Nj.f) (localizedHom K Q Nk.R Nk.f) :=
    H.affPullback Nj.R Nk.R Q G.R Nj.f Nk.f G.f G.g G.isPullback
  obtain ⟨l, hl₁, hl₂⟩ := hG.exists_lift a b hab
  have hc : localizedHom K (D.P j) G.R (G.f.comp Nj.g) ≫ E.π j =
      localizedHom K (D.P k) G.R (G.g.comp Nk.g) ≫ E.π k := by
    apply chart_compat H hX E
    rw [ty_comp, ty_comp, Category.assoc, Category.assoc, ← Nj.w, ← Nk.w,
      ← Category.assoc, ← Category.assoc, G.w]
  calc a ≫ coverValue hX E Q y j
      = l ≫ localizedHom K (D.P j) G.R (G.f.comp Nj.g) ≫ E.π j := by
        rw [← hl₁, H.comp (D.P j) Nj.R G.R Nj.g G.f]
        simp only [coverValue, Category.assoc]
        try rfl
    _ = l ≫ localizedHom K (D.P k) G.R (G.g.comp Nk.g) ≫ E.π k := by rw [hc]
    _ = b ≫ coverValue hX E Q y k := by
        rw [← hl₂, H.comp (D.P k) Nk.R G.R Nk.g G.g]
        simp only [coverValue, Category.assoc]
        try rfl

include H in
theorem exists_pointMap :
    ∃ g : localized K Q ⟶ E.Y, ∀ j, coverMap hX D Q y j ≫ g = coverValue hX E Q y j :=
  exists_glue_of_etale_cover (H.sheaf _ _) _ (coverMap hX D Q y) (coverMap_etale H hX D Q y)
    (coverMap_surj H hX D Q y) (coverValue hX E Q y) (coverValue_compat H hX E Q y)

/-- The map `Spec(B)ᵃⁿ → Y` attached to the point `y`, glued from the charts. -/
def pointMap : localized K Q ⟶ E.Y :=
  Classical.choose (exists_pointMap H hX E Q y)

theorem coverMap_pointMap (j : D.ι) :
    coverMap hX D Q y j ≫ pointMap H hX E Q y = coverValue hX E Q y j :=
  Classical.choose_spec (exists_pointMap H hX E Q y) j

/-- The key compatibility: along algebra maps identifying `y` with a chart point, the glued map
restricts to the chart quotient map. -/
theorem localizedHom_pointMap {Z : Type u} [CommRing Z] [Algebra K Z]
    (R : FinitePolynomialPresentation K Z) (i : D.ι) (β : B →ₐ[K] Z) (α : D.A i →ₐ[K] Z)
    (h : ty β ≫ pointHom K y = ty α ≫ pointHom K (D.x i)) :
    localizedHom K Q R β ≫ pointMap H hX E Q y = localizedHom K (D.P i) R α ≫ E.π i := by
  let z : RingPoints K X Z := RingPoints.changeRing β y
  have hz : pointHom K z = ty β ≫ pointHom K y := pointHom_changeRing β y
  apply ext_of_cover H hX D R z
  intro j
  let N' := coverModel hX D R z j
  let N := coverModel hX D Q y j
  obtain ⟨w, hw₁, hw₂⟩ := N.exists_lift (N'.f.comp β) N'.g (by
    rw [ty_comp, Category.assoc, ← N'.w]
    exact congrArg (fun t => ty N'.f ≫ t) hz.symm)
  calc coverMap hX D R z j ≫ localizedHom K Q R β ≫ pointMap H hX E Q y
      = localizedHom K Q N'.R (N'.f.comp β) ≫ pointMap H hX E Q y := by
        rw [H.comp, Category.assoc]
    _ = localizedHom K N.R N'.R w ≫ coverMap hX D Q y j ≫ pointMap H hX E Q y := by
        rw [← hw₁, H.comp, Category.assoc]
    _ = localizedHom K (D.P j) N'.R N'.g ≫ E.π j := by
        rw [coverMap_pointMap, coverValue, ← Category.assoc, ← H.comp, hw₂]
    _ = localizedHom K (D.P i) N'.R (N'.f.comp α) ≫ E.π i := by
        apply chart_compat H hX E
        rw [← N'.w, ty_comp, Category.assoc, ← h]
        exact congrArg (fun t => ty N'.f ≫ t) hz
    _ = coverMap hX D R z j ≫ localizedHom K (D.P i) R α ≫ E.π i := by
        rw [H.comp, Category.assoc]

end Cover

/-- The point family glued from the charts. -/
def pointFamily : PointFamily K X E.Y :=
  fun _ _ _ Q y => pointMap H hX E Q y

theorem pointFamily_naturality {A B : Type u} [CommRing A] [Algebra K A] [CommRing B]
    [Algebra K B] (P : FinitePolynomialPresentation K A) (Q : FinitePolynomialPresentation K B)
    (f : A →ₐ[K] B) (x : RingPoints K X A) :
    pointFamily H hX E B Q (RingPoints.changeRing f x) =
      localizedHom K P Q f ≫ pointFamily H hX E A P x := by
  let y := RingPoints.changeRing f x
  have hy : pointHom K y = ty f ≫ pointHom K x := pointHom_changeRing f x
  apply ext_of_cover H hX D Q y
  intro j
  let N := coverModel hX D Q y j
  change coverMap hX D Q y j ≫ pointMap H hX E Q y =
    coverMap hX D Q y j ≫ localizedHom K P Q f ≫ pointMap H hX E P x
  rw [coverMap_pointMap, ← Category.assoc, ← H.comp,
    localizedHom_pointMap H hX E P x N.R j (N.f.comp f) N.g (by
      rw [ty_comp, Category.assoc, ← hy, N.w])]

theorem pointFamily_etale {A : Type u} [CommRing A] [Algebra K A]
    (P : FinitePolynomialPresentation K A) (x : RingPoints K X A)
    (hx : AlgebraicSpace.IsEtale (pointHom K x)) :
    SaturatedAtlasPresentation.etale (pointFamily H hX E A P x) := by
  refine H.descent _ _ _ D.ι _ (coverMap hX D P x) (coverMap_etale H hX D P x)
    (coverMap_surj H hX D P x) (fun j => ?_)
  change etale (coverMap hX D P x j ≫ pointMap H hX E P x)
  rw [coverMap_pointMap]
  exact etale_comp (H.etaleFwd _ _ _ ((coverModel hX D P x j).etale_g hx)) (E.etale j)

theorem pointFamily_chart (i : D.ι) :
    pointFamily H hX E (D.A i) (D.P i) (D.x i) = E.π i := by
  have h := localizedHom_pointMap H hX E (D.P i) (D.x i) (D.P i) i (AlgHom.id K _)
    (AlgHom.id K _) rfl
  rwa [H.id, Category.id_comp, Category.id_comp] at h

theorem pointFamily_jointly_surjective (w : localizedSpaceFunctor.obj E.Y) :
    ∃ (A : Type u) (_ : CommRing A) (_ : Algebra K A) (P : FinitePolynomialPresentation K A)
      (x : RingPoints K X A), AlgebraicSpace.IsEtale (pointHom K x) ∧
        w ∈ Set.range (localizedSpaceFunctor.map (pointFamily H hX E A P x)) := by
  obtain ⟨i, hi⟩ := E.surj w
  refine ⟨D.A i, inferInstance, inferInstance, D.P i, D.x i, D.etale i, ?_⟩
  rwa [pointFamily_chart]

end Langlands.Analytic.SpaceAnalytification.ExistenceReduction
