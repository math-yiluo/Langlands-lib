import Langlands.Geometry.Analytic.SpaceAnalytificationExistenceConstruction
import Langlands.Geometry.Analytic.EtaleHomGluing

/-! # Fibre squares of affine test points go to pullbacks

For the point family glued from an analytic chart quotient, every presheaf fibre square of
affine test points of `X` is carried to a pullback square of analytic spaces. Joint monicity
of the two projections comes from the product model of the two test algebras; compatible
pairs of maps are lifted étale-locally through the chart covers and the chart quotient
squares.
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
  {X : AlgebraicSpace (Spec (CommRingCat.of K))} (H : AnalyticInputs K)
  (hX : IsSeparated X) {D : ChartData X} (E : QuotientData D)

section

variable {A B C : Type u} [CommRing A] [Algebra K A] [CommRing B] [Algebra K B]
  [CommRing C] [Algebra K C] (P : FinitePolynomialPresentation K A)
  (Q : FinitePolynomialPresentation K B) (R : FinitePolynomialPresentation K C)
  {f : A →ₐ[K] C} {g : B →ₐ[K] C}

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- The two composites `K → A → C` and `K → B → C` agree. -/
theorem comp_ofId_eq (f : A →ₐ[K] C) (g : B →ₐ[K] C) :
    f.comp (Algebra.ofId K A) = g.comp (Algebra.ofId K B) :=
  AlgHom.ext fun r => by simp only [AlgHom.comp_apply, Algebra.ofId_apply, AlgHom.commutes]

include H in
/-- The analytified projections of a presheaf fibre product of affine tests over any
presheaf are jointly monic. -/
theorem jointly_mono {F : AlgebraicSpace.Presheaf (Spec (CommRingCat.of K))}
    {u : (schemeYoneda (Spec (CommRingCat.of K))).obj (ringTest K A) ⟶ F}
    {v : (schemeYoneda (Spec (CommRingCat.of K))).obj (ringTest K B) ⟶ F}
    (hsq : IsPullback (ty f) (ty g) u v) (S : LocalizedCategory.{u, u, u} (K := K))
    (l m : S ⟶ localized K R) (h₁ : l ≫ localizedHom K P R f = m ≫ localizedHom K P R f)
    (h₂ : l ≫ localizedHom K Q R g = m ≫ localizedHom K Q R g) : l = m := by
  let P₀ : FinitePolynomialPresentation K K := FinitePolynomialPresentation.ofFiniteType K K
  let M := testModel P Q (Algebra.ofId K A) (Algebra.ofId K B)
  obtain ⟨k, hk₁, hk₂⟩ := M.exists_lift f g (by
    rw [← ty_comp, ← ty_comp, comp_ofId_eq f g])
  have hmono : Mono (ty k) := by
    constructor
    intro T a b hab
    apply hsq.hom_ext
    · rw [← hk₁, ty_comp, ← Category.assoc, hab, Category.assoc]
    · rw [← hk₂, ty_comp, ← Category.assoc, hab, Category.assoc]
  have hker : IsPullback (ty (AlgHom.id K C)) (ty (AlgHom.id K C)) (ty k) (ty k) := by
    rw [ty_id]
    exact IsKernelPair.id_of_mono (ty k)
  have hkerAn := H.affPullback R R M.R R k k (AlgHom.id K C) (AlgHom.id K C) hker
  rw [H.id] at hkerAn
  have hM := H.affPullback P Q P₀ M.R (Algebra.ofId K A) (Algebra.ofId K B) M.f M.g
    M.isPullback
  have hlm : l ≫ localizedHom K M.R R k = m ≫ localizedHom K M.R R k := by
    apply hM.hom_ext
    · rw [Category.assoc, Category.assoc, ← H.comp, hk₁, h₁]
    · rw [Category.assoc, Category.assoc, ← H.comp, hk₂, h₂]
  obtain ⟨t, ht₁, ht₂⟩ := hkerAn.exists_lift l m hlm
  rw [Category.comp_id] at ht₁ ht₂
  rw [← ht₁, ← ht₂]

end

include H in
/-- Compatible pairs of maps to `Spec(A)ᵃⁿ` and `Spec(B)ᵃⁿ` lift étale-locally to the
analytification of an affine model of `Spec A ×_X Spec B`. -/
theorem exists_local_lift {A B C : Type u} [CommRing A] [Algebra K A] [CommRing B]
    [Algebra K B] [CommRing C] [Algebra K C] (P : FinitePolynomialPresentation K A)
    (Q : FinitePolynomialPresentation K B) (R : FinitePolynomialPresentation K C)
    {f : A →ₐ[K] C} {g : B →ₐ[K] C} {x : RingPoints K X A} {y : RingPoints K X B}
    (hsq : IsPullback (ty f) (ty g) (pointHom K x) (pointHom K y))
    (S : LocalizedCategory.{u, u, u} (K := K)) (a : S ⟶ localized K P)
    (b : S ⟶ localized K Q) (hab : a ≫ pointMap H hX E P x = b ≫ pointMap H hX E Q y)
    (s : localizedSpaceFunctor.obj S) :
    ∃ (U : LocalizedCategory.{u, u, u} (K := K)) (e : U ⟶ S),
      etale e ∧ s ∈ Set.range (localizedSpaceFunctor.map e) ∧
        ∃ l : U ⟶ localized K R,
          l ≫ localizedHom K P R f = e ≫ a ∧ l ≫ localizedHom K Q R g = e ≫ b := by
  -- first étale base change, along the cover of `Spec(A)ᵃⁿ`
  obtain ⟨i, d, hd⟩ := coverMap_surj H hX D P x (localizedSpaceFunctor.map a s)
  obtain ⟨W₁, p₁, q₁, hpb₁, hq₁⟩ := H.base (coverMap hX D P x i) a (coverMap_etale H hX D P x i)
  obtain ⟨z₁, -, hz₁⟩ := H.points p₁ q₁ _ a hpb₁ (coverMap_etale H hX D P x i) d s hd
  -- second étale base change, along the cover of `Spec(B)ᵃⁿ`
  obtain ⟨j, d', hd'⟩ := coverMap_surj H hX D Q y (localizedSpaceFunctor.map (q₁ ≫ b) z₁)
  obtain ⟨W₂, p₂, q₂, hpb₂, hq₂⟩ :=
    H.base (coverMap hX D Q y j) (q₁ ≫ b) (coverMap_etale H hX D Q y j)
  obtain ⟨z₂, -, hz₂⟩ := H.points p₂ q₂ _ _ hpb₂ (coverMap_etale H hX D Q y j) d' z₁ hd'
  refine ⟨W₂, q₂ ≫ q₁, etale_comp hq₂ hq₁, ⟨z₂, ?_⟩, ?_⟩
  · rw [CategoryTheory.Functor.map_comp, TopCat.comp_app, hz₂, hz₁]
  let Ni := coverModel hX D P x i
  let Nj := coverModel hX D Q y j
  have hα : (q₂ ≫ p₁) ≫ coverMap hX D P x i = (q₂ ≫ q₁) ≫ a := by
    rw [Category.assoc, hpb₁.w, Category.assoc]
  have hβ : p₂ ≫ coverMap hX D Q y j = (q₂ ≫ q₁) ≫ b := by
    rw [hpb₂.w, Category.assoc]
  -- the chart quotient square
  let Mc := pointModel hX (D.P i) (D.P j) (D.x i) (D.x j)
  have hMc := E.pullback i j Mc.R Mc.f Mc.g Mc.isPullback
  obtain ⟨t, ht₁, ht₂⟩ := hMc.exists_lift
    ((q₂ ≫ p₁) ≫ localizedHom K (D.P i) Ni.R Ni.g) (p₂ ≫ localizedHom K (D.P j) Nj.R Nj.g) (by
      have h₁ : coverMap hX D P x i ≫ pointMap H hX E P x =
          localizedHom K (D.P i) Ni.R Ni.g ≫ E.π i := coverMap_pointMap H hX E P x i
      have h₂ : coverMap hX D Q y j ≫ pointMap H hX E Q y =
          localizedHom K (D.P j) Nj.R Nj.g ≫ E.π j := coverMap_pointMap H hX E Q y j
      have hα' : q₂ ≫ p₁ ≫ coverMap hX D P x i = q₂ ≫ q₁ ≫ a := by
        simpa only [Category.assoc] using hα
      have hβ' : p₂ ≫ coverMap hX D Q y j = q₂ ≫ q₁ ≫ b := by
        simpa only [Category.assoc] using hβ
      simp only [Category.assoc]
      rw [← h₁, ← h₂, reassoc_of% hα', reassoc_of% hβ', hab])
  -- two affine fibre products
  let G₁ := testModel Ni.R Mc.R Ni.g Mc.f
  have hG₁ := H.affPullback Ni.R Mc.R (D.P i) G₁.R Ni.g Mc.f G₁.f G₁.g G₁.isPullback
  obtain ⟨t₁, ht₁₁, ht₁₂⟩ := hG₁.exists_lift (q₂ ≫ p₁) t (by rw [ht₁, Category.assoc])
  let G₂ := testModel G₁.R Nj.R (G₁.g.comp Mc.g) Nj.g
  have hG₂ := H.affPullback G₁.R Nj.R (D.P j) G₂.R (G₁.g.comp Mc.g) Nj.g G₂.f G₂.g
    G₂.isPullback
  obtain ⟨t₂, ht₂₁, ht₂₂⟩ := hG₂.exists_lift t₁ p₂ (by
    rw [H.comp (D.P j) Mc.R G₁.R Mc.g G₁.g, ← Category.assoc, ht₁₂, ht₂])
  -- the comparison map from the model of `Spec A ×_X Spec B`
  obtain ⟨k, hk₁, hk₂⟩ := exists_algHom_of_isPullback hsq
    (G₂.f.comp (G₁.f.comp Ni.f)) (G₂.g.comp Nj.f) (by
      calc ty (G₂.f.comp (G₁.f.comp Ni.f)) ≫ pointHom K x
          = ty G₂.f ≫ ty G₁.f ≫ ty Ni.f ≫ pointHom K x := by
            rw [ty_comp (G₁.f.comp Ni.f) G₂.f, ty_comp Ni.f G₁.f]
            simp only [Category.assoc]
        _ = ty G₂.f ≫ ty G₁.f ≫ ty Ni.g ≫ pointHom K (D.x i) := by rw [Ni.w]
        _ = ty G₂.f ≫ ty G₁.g ≫ ty Mc.f ≫ pointHom K (D.x i) := by rw [reassoc_of% G₁.w]
        _ = ty G₂.f ≫ ty G₁.g ≫ ty Mc.g ≫ pointHom K (D.x j) := by rw [Mc.w]
        _ = ty G₂.f ≫ ty (G₁.g.comp Mc.g) ≫ pointHom K (D.x j) := by
            rw [← Category.assoc (ty G₁.g), ← ty_comp]
        _ = ty G₂.g ≫ ty Nj.g ≫ pointHom K (D.x j) := by rw [reassoc_of% G₂.w]
        _ = ty G₂.g ≫ ty Nj.f ≫ pointHom K y := by rw [← Nj.w]
        _ = ty (G₂.g.comp Nj.f) ≫ pointHom K y := by
            rw [ty_comp Nj.f G₂.g, Category.assoc])
  refine ⟨t₂ ≫ localizedHom K R G₂.R k, ?_, ?_⟩
  · rw [Category.assoc, ← H.comp, hk₁, H.comp P G₁.R G₂.R (G₁.f.comp Ni.f) G₂.f,
      H.comp P Ni.R G₁.R Ni.f G₁.f, ← Category.assoc, ht₂₁, ← Category.assoc, ht₁₁, hα]
  · rw [Category.assoc, ← H.comp, hk₂, H.comp Q Nj.R G₂.R Nj.f G₂.g, ← Category.assoc, ht₂₂,
      hβ]

include H in
/-- The glued point family carries fibre squares of affine test points to pullbacks. -/
theorem pointFamily_isPullback {A B C : Type u} [CommRing A] [Algebra K A] [CommRing B]
    [Algebra K B] [CommRing C] [Algebra K C] (P : FinitePolynomialPresentation K A)
    (Q : FinitePolynomialPresentation K B) (R : FinitePolynomialPresentation K C)
    (f : A →ₐ[K] C) (g : B →ₐ[K] C) (x : RingPoints K X A) (y : RingPoints K X B)
    (hsq : IsPullback (ty f) (ty g) (pointHom K x) (pointHom K y)) :
    IsPullback (localizedHom K P R f) (localizedHom K Q R g)
      (pointFamily H hX E A P x) (pointFamily H hX E B Q y) := by
  have hxy : RingPoints.changeRing f x = RingPoints.changeRing g y := by
    apply (uliftYonedaEquiv.{u + 1}).symm.injective
    change pointHom K (RingPoints.changeRing f x) = pointHom K (RingPoints.changeRing g y)
    rw [pointHom_changeRing, pointHom_changeRing, hsq.w]
  have hw : localizedHom K P R f ≫ pointFamily H hX E A P x =
      localizedHom K Q R g ≫ pointFamily H hX E B Q y := by
    rw [← pointFamily_naturality, ← pointFamily_naturality, hxy]
  exact isPullback_of_etale_local_lifts _ _ _ _ hw H.sheaf
    (jointly_mono H P Q R hsq)
    (fun S a b hab s => exists_local_lift H hX E P Q R hsq S a b hab s)

end Langlands.Analytic.SpaceAnalytification.ExistenceReduction
