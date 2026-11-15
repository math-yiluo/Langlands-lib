import Langlands.AlgebraicGeometry.UnramifiedFunctor.MurreChartsAffine
import Mathlib.RingTheory.HopkinsLevitzki

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite IsLocalRing

open scoped TensorProduct

noncomputable section

namespace Langlands.AlgebraicGeometry.UnramifiedFunctor.ArtinianBase

open Charts

variable {R : CommRingCat.{u}} {F : (Over (Spec R))ᵒᵖ ⥤ Type v}

/-- Restriction along an `R`-algebra map `φ : T → T'`, from `F(Spec T)` to `F(Spec T')`. -/
abbrev res {T T' : Type u} [CommRing T] [Algebra R T] [CommRing T'] [Algebra R T']
    (φ : T →ₐ[R] T') (x : F.obj (op (ovR R T))) : F.obj (op (ovR R T')) :=
  F.map (homR φ).op x

lemma res_res {T T' T'' : Type u} [CommRing T] [Algebra R T] [CommRing T'] [Algebra R T']
    [CommRing T''] [Algebra R T''] (φ : T →ₐ[R] T') (ψ : T' →ₐ[R] T'')
    (x : F.obj (op (ovR R T))) : res ψ (res φ x) = res (ψ.comp φ) x :=
  map_homR_map_homR φ ψ x

lemma homR_id {T : Type u} [CommRing T] [Algebra R T] : homR (AlgHom.id R T) = 𝟙 (ovR R T) := by
  ext1
  simp only [homR_left, Over.id_left]
  exact Spec.map_id _

lemma res_id {T : Type u} [CommRing T] [Algebra R T] (x : F.obj (op (ovR R T))) :
    res (AlgHom.id R T) x = x := by
  simp [res, homR_id]

lemma map_iso_injective {X Y : Over (Spec R)} (e : X ≅ Y) : Function.Injective (F.map e.hom.op) :=
  fun a b h ↦ by
    have := congrArg (F.map e.inv.op) h
    simpa [← Functor.map_comp_apply, ← op_comp] using this

section Tower

variable (M : Type u) [CommRing M] [Algebra R M]

lemma algebraOverBase_eq (B : Type u) [CommRing B] [Algebra M B] [Algebra R B]
    [IsScalarTower R M B] :
    algebraOverBase (ovR R M).hom B = (towerIso M B).hom ≫ homR (IsScalarTower.toAlgHom R M B) := by
  ext1
  simp [algebraOverBase]

lemma algHomOver_eq {B B' : Type u} [CommRing B] [Algebra M B] [Algebra R B]
    [IsScalarTower R M B] [CommRing B'] [Algebra M B'] [Algebra R B'] [IsScalarTower R M B']
    (φ : B →ₐ[M] B') :
    algHomOver (ovR R M).hom φ = (towerIso M B').hom ≫ homR (φ.restrictScalars R) ≫
      (towerIso M B).inv := by
  ext1
  simp [algHomOver]

lemma map_algHomOver_tower {B B' : Type u} [CommRing B] [Algebra M B] [Algebra R B]
    [IsScalarTower R M B] [CommRing B'] [Algebra M B'] [Algebra R B'] [IsScalarTower R M B']
    (φ : B →ₐ[M] B') (x : F.obj (op (ovR R B))) :
    F.map (algHomOver (ovR R M).hom φ).op (F.map (towerIso M B).hom.op x) =
      F.map (towerIso M B').hom.op (res (φ.restrictScalars R) x) := by
  rw [← Functor.map_comp_apply, ← op_comp, algHomOver_eq, Category.assoc, Category.assoc,
    Iso.inv_hom_id, Category.comp_id, op_comp, Functor.map_comp_apply]

end Tower

/-- Strong (F5) for an `R`-algebra which is a local artinian ring. -/
lemma nilInj (h5 : NilpotentInjective F) (A : Type u) [CommRing A] [Algebra R A] [IsLocalRing A]
    [IsArtinianRing A] (I : Ideal A) (hI : IsNilpotent I) :
    Function.Injective (res (F := F) (Ideal.Quotient.mkₐ R I)) := by
  have h := h5 A I hI (ovR R A).hom
  rw [algebraOverBase_eq] at h
  intro a b hab
  apply h
  simp only [op_comp, Functor.map_comp_apply]
  exact congrArg _ hab


/-- With (F1b), restriction along a map of fields is injective. -/
lemma fieldInj (hF : FaithfullyFlatSheaf F) {K L : Type u} [Field K] [Algebra R K] [Field L]
    [Algebra R L] (φ : K →ₐ[R] L) : Function.Injective (res (F := F) φ) :=
  map_injective_of_field hF _ (homR φ)

/-- Two elements of `F(Spec T)` agree at every point of `Spec T` with values in a field. -/
def FieldAgree {T : Type u} [CommRing T] [Algebra R T] (w₁ w₂ : F.obj (op (ovR R T))) : Prop :=
  ∀ (K : Type u) [Field K] [Algebra R K] (ψ : T →ₐ[R] K), res ψ w₁ = res ψ w₂

lemma FieldAgree.restrict {T T' : Type u} [CommRing T] [Algebra R T] [CommRing T'] [Algebra R T']
    {w₁ w₂ : F.obj (op (ovR R T))} (h : FieldAgree w₁ w₂) (φ : T →ₐ[R] T') :
    FieldAgree (res φ w₁) (res φ w₂) := fun K _ _ ψ ↦ by
  rw [res_res, res_res]
  exact h K (ψ.comp φ)

/-- For a local artinian `T`, agreement at the residue field gives equality (strong (F5)). -/
lemma eq_of_residue_local (h5 : NilpotentInjective F) {T : Type u} [CommRing T] [Algebra R T]
    [IsLocalRing T] [IsArtinianRing T] {w₁ w₂ : F.obj (op (ovR R T))}
    (h : res (Ideal.Quotient.mkₐ R (maximalIdeal T)) w₁ =
      res (Ideal.Quotient.mkₐ R (maximalIdeal T)) w₂) : w₁ = w₂ :=
  nilInj h5 T (maximalIdeal T) ((isArtinianRing_iff_isNilpotent_maximalIdeal T).mp inferInstance) h

lemma eq_of_fieldAgree_local (h5 : NilpotentInjective F) {T : Type u} [CommRing T] [Algebra R T]
    [IsLocalRing T] [IsArtinianRing T] {w₁ w₂ : F.obj (op (ovR R T))} (h : FieldAgree w₁ w₂) :
    w₁ = w₂ :=
  letI : Field (T ⧸ maximalIdeal T) := Ideal.Quotient.field _
  eq_of_residue_local h5 (h (T ⧸ maximalIdeal T) (Ideal.Quotient.mkₐ R (maximalIdeal T)))


section Artinian

/-- In an artinian ring, for every maximal ideal `𝔫` some element lies outside `𝔫` and inside
every other maximal ideal. -/
lemma exists_sep (T : Type u) [CommRing T] [IsArtinianRing T] (𝔫 : MaximalSpectrum T) :
    ∃ s : T, s ∉ 𝔫.asIdeal ∧ ∀ 𝔪 : MaximalSpectrum T, 𝔪 ≠ 𝔫 → s ∈ 𝔪.asIdeal := by
  classical
  have := Fintype.ofFinite (MaximalSpectrum T)
  have H : ∀ 𝔪 : MaximalSpectrum T, 𝔪 ≠ 𝔫 → ∃ a ∈ 𝔪.asIdeal, a ∉ 𝔫.asIdeal := by
    intro 𝔪 h
    by_contra! H
    exact h (MaximalSpectrum.ext (𝔪.isMaximal.eq_of_le 𝔫.isMaximal.ne_top H))
  choose a ha ha' using H
  let b : MaximalSpectrum T → T := fun 𝔪 ↦ if h : 𝔪 = 𝔫 then 1 else a 𝔪 h
  have h𝔫 := 𝔫.isMaximal.isPrime
  refine ⟨∏ 𝔪, b 𝔪, ?_, ?_⟩
  · rw [Ideal.IsPrime.prod_mem_iff]
    rintro ⟨𝔪, -, h𝔪⟩
    by_cases h : 𝔪 = 𝔫
    · simp only [b, h, ↓reduceDIte] at h𝔪
      exact 𝔫.isMaximal.ne_top ((Ideal.eq_top_iff_one _).mpr h𝔪)
    · simp only [b, h, ↓reduceDIte] at h𝔪
      exact ha' 𝔪 h h𝔪
  · intro 𝔪 h
    have h𝔪 := 𝔪.isMaximal.isPrime
    rw [Ideal.IsPrime.prod_mem_iff]
    exact ⟨𝔪, Finset.mem_univ _, by simp only [b, h, ↓reduceDIte]; exact ha 𝔪 h⟩

/-- The localization of an artinian ring away from an element lying in exactly all maximal
ideals but one is local. -/
lemma isLocalRing_away {T : Type u} [CommRing T] [IsArtinianRing T] (𝔫 : MaximalSpectrum T)
    (s : T) (hs : s ∉ 𝔫.asIdeal) (hs' : ∀ 𝔪 : MaximalSpectrum T, 𝔪 ≠ 𝔫 → s ∈ 𝔪.asIdeal) :
    IsLocalRing (Localization.Away s) := by
  have hdisj : Disjoint (Submonoid.powers s : Set T) 𝔫.asIdeal := by
    rw [Set.disjoint_left]
    rintro _ ⟨n, rfl⟩ h
    exact hs (𝔫.isMaximal.isPrime.mem_of_pow_mem n h)
  have hP := IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers s)
    (Localization.Away s) 𝔫.asIdeal 𝔫.isMaximal.isPrime hdisj
  have : Nontrivial (Localization.Away s) := by
    by_contra hn
    rw [not_nontrivial_iff_subsingleton] at hn
    exact hP.ne_top (Subsingleton.elim _ _)
  have : Nonempty (MaximalSpectrum (Localization.Away s)) :=
    ⟨⟨_, (Ideal.exists_maximal (Localization.Away s)).choose_spec⟩⟩
  have key : ∀ M : MaximalSpectrum (Localization.Away s),
      M.asIdeal.under T = 𝔫.asIdeal := by
    intro M
    have hpr : (M.asIdeal.under T).IsPrime := Ideal.IsPrime.under T M.asIdeal
    have hmax : (M.asIdeal.under T).IsMaximal := IsArtinianRing.isMaximal_of_isPrime _
    by_contra hne
    have hsm := hs' ⟨_, hmax⟩ (fun h ↦ hne (congrArg MaximalSpectrum.asIdeal h))
    exact M.isMaximal.ne_top (Ideal.eq_top_of_isUnit_mem _ hsm
      (IsLocalization.Away.algebraMap_isUnit s))
  have : Subsingleton (MaximalSpectrum (Localization.Away s)) := ⟨fun M₁ M₂ ↦ by
    ext1
    rw [← IsLocalization.map_under (Submonoid.powers s) (Localization.Away s) M₁.asIdeal,
      ← IsLocalization.map_under (Submonoid.powers s) (Localization.Away s) M₂.asIdeal,
      key M₁, key M₂]⟩
  exact IsLocalRing.of_singleton_maximalSpectrum

/-- (F1a) and strong (F5): two elements of `F(Spec T)`, `T` artinian, which agree at every
point with values in a field are equal. -/
lemma eq_of_fieldAgree (hZ : ZariskiSheaf F) (h5 : NilpotentInjective F) {T : Type u}
    [CommRing T] [Algebra R T] [IsArtinianRing T] {w₁ w₂ : F.obj (op (ovR R T))}
    (h : FieldAgree w₁ w₂) : w₁ = w₂ := by
  choose s hs hs' using exists_sep T
  have hspan : Ideal.span (Set.range s) = ⊤ := by
    by_contra hne
    obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
    exact hs ⟨M, hM⟩ (hle (Ideal.subset_span ⟨⟨M, hM⟩, rfl⟩))
  let 𝒰 := (Scheme.affineOpenCoverOfSpanRangeEqTop (R := CommRingCat.of T) s hspan).openCover
  refine (hZ (ovR R T) 𝒰).isSeparatedFor.ext fun Y g hg ↦ ?_
  obtain ⟨i⟩ := hg
  have := isLocalRing_away i (s i) (hs i) (hs' i)
  have e : (Over.homMk (𝒰.f i) : Over.mk (𝒰.f i ≫ (ovR R T).hom) ⟶ ovR R T) =
      (towerIso T (Localization.Away (s i))).hom ≫
        homR (IsScalarTower.toAlgHom R T (Localization.Away (s i))) := by
    ext1
    simp [𝒰]
    rfl
  have key := eq_of_fieldAgree_local h5
    (h.restrict (IsScalarTower.toAlgHom R T (Localization.Away (s i))))
  rw [e]
  erw [op_comp, Functor.map_comp_apply, Functor.map_comp_apply]
  exact congrArg _ key

end Artinian

section Descent

open Algebra.TensorProduct

/-- (F1b) for a faithfully flat algebra `C → P`: an element of `F(Spec P)` whose two pullbacks
to `F(Spec (P ⊗_C P))` agree comes from `F(Spec C)`. -/
lemma flatDescent (hF : FaithfullyFlatSheaf F) (C P : Type u) [CommRing C] [CommRing P]
    [Algebra R C] [Algebra C P] [Algebra R P] [IsScalarTower R C P] [Module.FaithfullyFlat C P]
    (w : F.obj (op (ovR R P)))
    (hw : res (includeLeft (R := C) (S := R) (A := P) (B := P)) w =
      res ((includeRight (R := C) (A := P) (B := P)).restrictScalars R) w) :
    ∃ w₀ : F.obj (op (ovR R C)), res (IsScalarTower.toAlgHom R C P) w₀ = w := by
  let g : ovR R P ⟶ ovR R C := homR (IsScalarTower.toAlgHom R C P)
  have hff : Flat g.left ∧ Surjective g.left :=
    (flat_and_surjective_SpecMap_iff (CommRingCat.ofHom (algebraMap C P))).mpr
      (RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance)
  have : Flat g.left := hff.1
  have : Surjective g.left := hff.2
  have : QuasiCompact g.left :=
    (inferInstance : QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap C P))))
  obtain ⟨w₀, hw₀, -⟩ := Presieve.isSheafFor_singleton.mp (hF g hff.1 hff.2 this) w
    (by
      intro Z p₁ p₂ hp
      have hcond : p₁.left ≫ Spec.map (CommRingCat.ofHom (algebraMap C P)) =
          p₂.left ≫ Spec.map (CommRingCat.ofHom (algebraMap C P)) :=
        congrArg CommaMorphism.left hp
      let l := pullback.lift p₁.left p₂.left hcond ≫ (pullbackSpecIso C P P).hom
      have hl₁ : l ≫ Spec.map (CommRingCat.ofHom
          (includeLeft (R := C) (S := R) (A := P) (B := P)).toRingHom) = p₁.left := by
        simp only [l, Category.assoc]
        erw [pullbackSpecIso_hom_fst]
        exact pullback.lift_fst _ _ _
      have hl₂ : l ≫ Spec.map (CommRingCat.ofHom
          ((includeRight (R := C) (A := P) (B := P)).restrictScalars R).toRingHom) = p₂.left := by
        simp only [l, Category.assoc]
        erw [pullbackSpecIso_hom_snd]
        exact pullback.lift_snd _ _ _
      have hbase : (ovR R (P ⊗[C] P)).hom = Spec.map (CommRingCat.ofHom
          (includeLeft (R := C) (S := R) (A := P) (B := P)).toRingHom) ≫ (ovR R P).hom := by
        change Spec.map _ = Spec.map _ ≫ Spec.map _
        rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
        congr 2
      let h' : Z ⟶ ovR R (P ⊗[C] P) := Over.homMk l (by
        rw [hbase, ← Category.assoc, hl₁]
        exact Over.w p₁)
      have e₁ : p₁ = h' ≫ homR (includeLeft (R := C) (S := R) (A := P) (B := P)) := by
        ext1
        exact hl₁.symm
      have e₂ : p₂ = h' ≫ homR ((includeRight (R := C) (A := P) (B := P)).restrictScalars R) := by
        ext1
        exact hl₂.symm
      rw [e₁, e₂, op_comp, op_comp, Functor.map_comp_apply, Functor.map_comp_apply]
      exact congrArg _ hw)
  exact ⟨w₀, hw₀⟩

end Descent


section Prod

/-- (F1a): on an object over the empty scheme, `F` has at most one element. -/
lemma subsingleton_of_isEmpty (hZ : ZariskiSheaf F) (Z : Over (Spec R)) [IsEmpty Z.left] :
    Subsingleton (F.obj (op Z)) := by
  let 𝒰 : Scheme.OpenCover.{u} Z.left :=
    Scheme.Cover.mkOfCovers PEmpty.{u + 1} (fun _ => Z.left) (fun _ => 𝟙 Z.left)
      (fun x => isEmptyElim x)
  refine ⟨fun a b ↦ (hZ Z 𝒰).isSeparatedFor.ext fun Y g hg ↦ ?_⟩
  obtain ⟨i⟩ := hg
  change PEmpty.{u + 1} at i
  exact isEmptyElim i

/-- For an `R`-algebra map `φ : T → T'`, the object `Spec T' ⟶ Spec T ⟶ Spec R` is `ovR T'`. -/
def specIso {T T' : Type u} [CommRing T] [Algebra R T] [CommRing T'] [Algebra R T']
    (φ : T →ₐ[R] T') :
    Over.mk (Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ (ovR R T).hom) ≅ ovR R T' :=
  Over.isoMk (Iso.refl _) (by
    change 𝟙 _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [Category.id_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext r
    exact (φ.commutes r).symm)

lemma homMk_eq {T T' : Type u} [CommRing T] [Algebra R T] [CommRing T'] [Algebra R T']
    (φ : T →ₐ[R] T') :
    (Over.homMk (Spec.map (CommRingCat.ofHom φ.toRingHom)) :
      Over.mk (Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ (ovR R T).hom) ⟶ ovR R T) =
      (specIso φ).hom ≫ homR φ := by
  ext1
  simp [specIso]

lemma comap_fst_ne_comap_snd {A B : Type u} [CommRing A] [CommRing B] (p : PrimeSpectrum A)
    (q : PrimeSpectrum B) :
    PrimeSpectrum.comap (RingHom.fst A B) p ≠ PrimeSpectrum.comap (RingHom.snd A B) q := by
  intro h
  have h1 : ((0, 1) : A × B) ∈ (PrimeSpectrum.comap (RingHom.fst A B) p).asIdeal := by
    simp [p.asIdeal.zero_mem]
  have h2 : ((1, 0) : A × B) ∈ (PrimeSpectrum.comap (RingHom.snd A B) q).asIdeal := by
    simp [q.asIdeal.zero_mem]
  rw [h] at h1
  have := (PrimeSpectrum.comap (RingHom.snd A B) q).asIdeal.add_mem h2 h1
  simp only [Prod.mk_add_mk, add_zero, zero_add] at this
  exact (PrimeSpectrum.comap (RingHom.snd A B) q).isPrime.ne_top
    ((Ideal.eq_top_iff_one _).mpr (by simpa [Prod.one_eq_mk] using this))

/-- (F1a) for a product: elements of `F(Spec A)` and `F(Spec B)` glue to `F(Spec (A × B))`. -/
lemma exists_prod (hZ : ZariskiSheaf F) (A B : Type u) [CommRing A] [Algebra R A] [CommRing B]
    [Algebra R B] (a : F.obj (op (ovR R A))) (b : F.obj (op (ovR R B))) :
    ∃ w : F.obj (op (ovR R (A × B))), res (AlgHom.fst R A B) w = a ∧
      res (AlgHom.snd R A B) w = b := by
  let Rj : ULift.{u} Bool → CommRingCat.{u} := fun j ↦ cond j.down (CommRingCat.of A) (CommRingCat.of B)
  let g : (j : ULift.{u} Bool) → CommRingCat.of (A × B) ⟶ Rj j := fun j ↦
    match j with
    | ⟨true⟩ => CommRingCat.ofHom (RingHom.fst A B)
    | ⟨false⟩ => CommRingCat.ofHom (RingHom.snd A B)
  have hg : ∀ j, IsOpenImmersion (Spec.map (g j)) := by
    rintro ⟨j⟩
    cases j
    · let := (RingHom.snd A B).toAlgebra
      exact IsOpenImmersion.of_isLocalization (S := B) ((0, 1) : A × B)
    · let := (RingHom.fst A B).toAlgebra
      exact IsOpenImmersion.of_isLocalization (S := A) ((1, 0) : A × B)
  let 𝒰 : (ovR R (A × B)).left.OpenCover :=
    Scheme.Cover.mkOfCovers (ULift.{u} Bool) (fun j ↦ Spec (Rj j)) (fun j ↦ Spec.map (g j)) (by
        intro x
        obtain ⟨y, rfl⟩ := (PrimeSpectrum.primeSpectrumProd A B).symm.surjective x
        rcases y with y | y
        · exact ⟨⟨true⟩, y, (PrimeSpectrum.primeSpectrumProd_symm_inl y).symm⟩
        · exact ⟨⟨false⟩, y, (PrimeSpectrum.primeSpectrumProd_symm_inr y).symm⟩) hg
  have hS := (Presieve.isSheafFor_arrows_iff _ _).mp (hZ (ovR R (A × B)) 𝒰)
  have e₁ : (Over.homMk (𝒰.f ⟨true⟩) : Over.mk (𝒰.f ⟨true⟩ ≫ (ovR R (A × B)).hom) ⟶ _) =
      (specIso (AlgHom.fst R A B)).hom ≫ homR (AlgHom.fst R A B) :=
    homMk_eq (AlgHom.fst R A B)
  have e₂ : (Over.homMk (𝒰.f ⟨false⟩) : Over.mk (𝒰.f ⟨false⟩ ≫ (ovR R (A × B)).hom) ⟶ _) =
      (specIso (AlgHom.snd R A B)).hom ≫ homR (AlgHom.snd R A B) :=
    homMk_eq (AlgHom.snd R A B)
  let x : (j : ULift.{u} Bool) → F.obj (op (Over.mk (𝒰.f j ≫ (ovR R (A × B)).hom))) := fun j ↦
    match j with
    | ⟨true⟩ => F.map (specIso (AlgHom.fst R A B)).hom.op a
    | ⟨false⟩ => F.map (specIso (AlgHom.snd R A B)).hom.op b
  obtain ⟨w, hw, -⟩ := hS x (by
    intro i j Z gi gj hij
    by_cases h : i = j
    · subst h
      have : Mono (Over.homMk (𝒰.f i) : Over.mk (𝒰.f i ≫ (ovR R (A × B)).hom) ⟶ _) := by
        have : Mono (𝒰.f i) := inferInstance
        exact Over.mono_of_mono_left _
      rw [cancel_mono] at hij
      rw [hij]
    · have : IsEmpty Z.left := by
        constructor
        intro z
        have hz := congrArg (fun k ↦ k.left z) hij
        simp only [Over.comp_left, Over.homMk_left, Scheme.Hom.comp_apply] at hz
        obtain ⟨i⟩ := i
        obtain ⟨j⟩ := j
        cases i <;> cases j
        · exact h rfl
        · exact comap_fst_ne_comap_snd _ _ hz.symm
        · exact comap_fst_ne_comap_snd _ _ hz
        · exact h rfl
      exact Subsingleton.elim (h := subsingleton_of_isEmpty hZ Z) _ _)
  refine ⟨w, ?_, ?_⟩
  · have := hw ⟨true⟩
    rw [e₁] at this
    apply map_iso_injective (specIso (AlgHom.fst R A B))
    rw [res, ← Functor.map_comp_apply, ← op_comp]
    exact this
  · have := hw ⟨false⟩
    rw [e₂] at this
    apply map_iso_injective (specIso (AlgHom.snd R A B))
    rw [res, ← Functor.map_comp_apply, ← op_comp]
    exact this

end Prod


section Over

variable {C X ℓ : Type u} [CommRing C] [Algebra R C] [CommRing X] [Algebra R X] [CommRing ℓ]
  [Algebra R ℓ]

/-- `w ∈ F(Spec X)` lies over `η ∈ F(Spec ℓ)` along `ι : C → X` and `π : C → ℓ`: at every point
`ψ : X → K` with values in a field, `w` restricts to the restriction of `η` along any
`ψ₀ : ℓ → K` with `ψ₀ ∘ π = ψ ∘ ι`. -/
def IsOver (ι : C →ₐ[R] X) (π : C →ₐ[R] ℓ) (η : F.obj (op (ovR R ℓ)))
    (w : F.obj (op (ovR R X))) : Prop :=
  ∀ (K : Type u) [Field K] [Algebra R K] (ψ : X →ₐ[R] K) (ψ₀ : ℓ →ₐ[R] K),
    ψ₀.comp π = ψ.comp ι → res ψ w = res ψ₀ η

lemma IsOver.restrict {ι : C →ₐ[R] X} {π : C →ₐ[R] ℓ} {η : F.obj (op (ovR R ℓ))}
    {w : F.obj (op (ovR R X))} (h : IsOver ι π η w) {Y : Type u} [CommRing Y] [Algebra R Y]
    (φ : X →ₐ[R] Y) : IsOver (φ.comp ι) π η (res φ w) := fun K _ _ ψ ψ₀ hψ ↦ by
  rw [res_res]
  exact h K (ψ.comp φ) ψ₀ hψ

lemma isOver_of_res {π : C →ₐ[R] ℓ} {η : F.obj (op (ovR R ℓ))} {w : F.obj (op (ovR R C))}
    (h : res π w = η) : IsOver (AlgHom.id R C) π η w := fun K _ _ ψ ψ₀ hψ ↦ by
  rw [← h, res_res, hψ]
  rfl

lemma IsOver.res_eq {ℓ' : Type u} [Field ℓ'] [Algebra R ℓ'] {π : C →ₐ[R] ℓ'}
    {η : F.obj (op (ovR R ℓ'))} {w : F.obj (op (ovR R C))}
    (h : IsOver (AlgHom.id R C) π η w) : res π w = η := by
  have := h ℓ' π (AlgHom.id R ℓ') rfl
  rwa [res_id] at this

end Over

section ArtLift

open Algebra.TensorProduct

/-- A morphism from a local artinian ring to a field kills the maximal ideal. -/
lemma isNilpotent_of_mem_maximalIdeal {N : Type u} [CommRing N] [IsLocalRing N]
    [IsArtinianRing N] {x : N} (hx : x ∈ maximalIdeal N) : IsNilpotent x := by
  obtain ⟨n, hn⟩ := (isArtinianRing_iff_isNilpotent_maximalIdeal N).mp inferInstance
  refine ⟨n, ?_⟩
  have := Ideal.pow_mem_pow hx n
  rw [hn] at this
  simpa using this

lemma map_maximalIdeal_eq_zero {N K : Type u} [CommRing N] [IsLocalRing N] [IsArtinianRing N]
    [Field K] (ψ : N →+* K) {x : N} (hx : x ∈ maximalIdeal N) : ψ x = 0 :=
  ((isNilpotent_of_mem_maximalIdeal hx).map ψ).eq_zero

/-- Condition (F4′) in terms of `IsOver`. Let `π : C → ℓ` be a surjection from a local ring onto
a field, `η ∈ F(Spec ℓ)`, `N` a local artinian ring with `j : C → N` inducing a surjection onto
the residue field of `N`, and `N ⊆ A'` with `length_N (A'/N) = 1`. An element of `F(Spec A')`
over `η` gives an element of `F(Spec N)` over `η`. -/
lemma artLift (h4 : ArtinianLifting F) (hZ : ZariskiSheaf F) (h5 : NilpotentInjective F)
    {C ℓ : Type u} [CommRing C] [IsLocalRing C] [Algebra R C] [Field ℓ] [Algebra R ℓ]
    (π : C →ₐ[R] ℓ) (hπ : Function.Surjective π) (η : F.obj (op (ovR R ℓ)))
    (N A' : Type u) [CommRing N] [IsLocalRing N] [IsArtinianRing N] [Algebra R N] [CommRing A']
    [Algebra N A'] [Algebra R A'] [IsScalarTower R N A'] [Module.Finite N A']
    (j : C →ₐ[R] N) (hj : Function.Surjective ((residue N).comp j.toRingHom))
    (hinj : Function.Injective (algebraMap N A'))
    (hlen : Module.length N (A' ⧸ LinearMap.range (Algebra.linearMap N A')) = 1)
    (w' : F.obj (op (ovR R A'))) (hw' : IsOver ((IsScalarTower.toAlgHom R N A').comp j) π η w') :
    ∃ w : F.obj (op (ovR R N)), IsOver j π η w := by
  let ρ : N →ₐ[R] ResidueField N := IsScalarTower.toAlgHom R N (ResidueField N)
  have hker : RingHom.ker π ≤ RingHom.ker (ρ.comp j) := by
    have h1 : RingHom.ker π = maximalIdeal C :=
      IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective _ hπ)
    have h2 : RingHom.ker (ρ.comp j) = maximalIdeal C :=
      IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective _ hj)
    rw [h1, h2]
  let θ : ℓ →ₐ[R] ResidueField N :=
    (Ideal.Quotient.liftₐ (RingHom.ker π) (ρ.comp j) (fun a ha ↦ hker ha)).comp
      (Ideal.quotientKerAlgEquivOfSurjective hπ).symm.toAlgHom
  have hθ : θ.comp π = ρ.comp j := by
    ext c
    have : (Ideal.quotientKerAlgEquivOfSurjective hπ).symm (π c) =
        Ideal.Quotient.mk (RingHom.ker π) c :=
      (AlgEquiv.symm_apply_eq _).mpr rfl
    change (Ideal.Quotient.liftₐ (RingHom.ker π) (ρ.comp j) (fun a ha ↦ hker ha))
      ((Ideal.quotientKerAlgEquivOfSurjective hπ).symm (π c)) = ρ (j c)
    rw [this]
    rfl
  let ξ₀ : F.obj (op (ovR R (ResidueField N))) := res θ η
  have : IsArtinianRing (A' ⊗[N] ResidueField N) :=
    IsArtinianRing.of_finite N (A' ⊗[N] ResidueField N)
  let iL : A' →ₐ[R] A' ⊗[N] ResidueField N := includeLeft (R := N) (S := R)
  let iR : ResidueField N →ₐ[R] A' ⊗[N] ResidueField N :=
    (includeRight (R := N) (A := A') (B := ResidueField N)).restrictScalars R
  have key : ∀ n : N, iR (ρ n) = iL (algebraMap N A' n) := fun n ↦ by
    simp only [iR, iL, ρ, AlgHom.coe_restrictScalars', includeRight_apply, includeLeft_apply,
      IsScalarTower.coe_toAlgHom']
    rw [← Algebra.TensorProduct.algebraMap_apply', Algebra.TensorProduct.algebraMap_apply]
  have hagree : res iL w' = res iR ξ₀ := eq_of_fieldAgree hZ h5 (fun K _ _ ψ ↦ by
    simp only [ξ₀, res_res]
    apply hw' K (ψ.comp iL) (ψ.comp (iR.comp θ))
    ext c
    have h1 := congrArg (fun f ↦ f c) hθ
    simp only [AlgHom.comp_apply] at h1 ⊢
    rw [h1, key]
    rfl)
  obtain ⟨ξ, hξ⟩ := h4 N (ovR R N).hom A' hinj hlen
    (F.map (towerIso N (ResidueField N)).hom.op ξ₀) (F.map (towerIso N A').hom.op w') (by
      rw [map_algHomOver_tower, map_algHomOver_tower]
      exact congrArg _ hagree)
  have hξ' : res ρ ξ = ξ₀ := by
    rw [algebraOverBase_eq, op_comp, Functor.map_comp_apply] at hξ
    exact map_iso_injective _ hξ
  refine ⟨ξ, fun K _ _ ψ ψ₀ hψ ↦ ?_⟩
  let ψbar : ResidueField N →ₐ[R] K := Ideal.Quotient.liftₐ (maximalIdeal N) ψ
    (fun x hx ↦ map_maximalIdeal_eq_zero ψ.toRingHom hx)
  have hψ' : ψbar.comp ρ = ψ := by
    ext
    rfl
  have hψ₀ : ψbar.comp θ = ψ₀ := by
    ext x
    obtain ⟨c, rfl⟩ := hπ x
    have h1 := congrArg (fun f ↦ f c) hθ
    have h2 := congrArg (fun f ↦ f c) hψ
    simp only [AlgHom.comp_apply] at h1 h2 ⊢
    rw [h1, h2]
    rfl
  rw [← hψ', ← res_res, hξ']
  simp only [ξ₀]
  rw [res_res, hψ₀]

end ArtLift

end Langlands.AlgebraicGeometry.UnramifiedFunctor.ArtinianBase
