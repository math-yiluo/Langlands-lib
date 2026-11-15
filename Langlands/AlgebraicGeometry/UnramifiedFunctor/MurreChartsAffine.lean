import Langlands.AlgebraicGeometry.UnramifiedFunctor.MurreChartsLocalization
import Langlands.AlgebraicGeometry.UnramifiedFunctor.MurreChartsLocal

/-! # Affine test objects over `Spec R`

For a ring `R`, an `R`-algebra `T` gives the object `ovR T = (Spec T ⟶ Spec R)` of
`Over (Spec R)`, and an `R`-algebra map `φ : T → T'` gives `homR φ : ovR T' ⟶ ovR T`.
This module restates condition (F2) for localizations in these terms, proves that (F1b)
makes restriction along field extensions injective, and records the open immersions
`Spec A[1/b] ⟶ Spec A[1/a]` for `a ∣ b`. -/

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

noncomputable section

namespace Langlands.AlgebraicGeometry.UnramifiedFunctor

namespace Charts

variable {R : CommRingCat.{u}}

/-- An `R`-algebra `T` as the object `Spec T ⟶ Spec R` of `Over (Spec R)`. -/
abbrev ovR (R : CommRingCat.{u}) (T : Type u) [CommRing T] [Algebra R T] : Over (Spec R) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R T)) : Spec (CommRingCat.of T) ⟶ Spec R)

/-- An `R`-algebra map `φ : T → T'` as the morphism `Spec T' ⟶ Spec T` over `Spec R`. -/
def homR {T T' : Type u} [CommRing T] [Algebra R T] [CommRing T'] [Algebra R T']
    (φ : T →ₐ[R] T') : ovR R T' ⟶ ovR R T :=
  Over.homMk (Spec.map (CommRingCat.ofHom φ.toRingHom)) (by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext r
    exact φ.commutes r)

@[simp]
lemma homR_left {T T' : Type u} [CommRing T] [Algebra R T] [CommRing T'] [Algebra R T']
    (φ : T →ₐ[R] T') : (homR φ).left = Spec.map (CommRingCat.ofHom φ.toRingHom) := rfl

lemma homR_comp {T T' T'' : Type u} [CommRing T] [Algebra R T] [CommRing T'] [Algebra R T']
    [CommRing T''] [Algebra R T''] (φ : T →ₐ[R] T') (ψ : T' →ₐ[R] T'') :
    homR (ψ.comp φ) = homR ψ ≫ homR φ := by
  ext1
  simp only [homR_left, Over.comp_left, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

lemma map_homR_map_homR {F : (Over (Spec R))ᵒᵖ ⥤ Type v} {T T' T'' : Type u} [CommRing T]
    [Algebra R T] [CommRing T'] [Algebra R T'] [CommRing T''] [Algebra R T'']
    (φ : T →ₐ[R] T') (ψ : T' →ₐ[R] T'') (x : F.obj (op (ovR R T))) :
    F.map (homR ψ).op (F.map (homR φ).op x) = F.map (homR (ψ.comp φ)).op x := by
  rw [homR_comp, op_comp, Functor.map_comp_apply]

/-- For `R → A → T`, the object `Spec T ⟶ Spec A ⟶ Spec R` is `ovR T`. -/
def towerIso (A T : Type u) [CommRing A] [Algebra R A] [CommRing T] [Algebra A T]
    [Algebra R T] [IsScalarTower R A T] :
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap A T)) ≫
      (Spec.map (CommRingCat.ofHom (algebraMap R A)) : Spec (CommRingCat.of A) ⟶ Spec R)) ≅
        ovR R T :=
  Over.isoMk (Iso.refl _) (by
    change 𝟙 _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [Category.id_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← IsScalarTower.algebraMap_eq])

@[simp]
lemma towerIso_hom_left (A T : Type u) [CommRing A] [Algebra R A] [CommRing T] [Algebra A T]
    [Algebra R T] [IsScalarTower R A T] : (towerIso (R := R) A T).hom.left = 𝟙 _ := rfl

@[simp]
lemma towerIso_inv_left (A T : Type u) [CommRing A] [Algebra R A] [CommRing T] [Algebra A T]
    [Algebra R T] [IsScalarTower R A T] : (towerIso (R := R) A T).inv.left = 𝟙 _ := rfl

section F2

variable {F : (Over (Spec R))ᵒᵖ ⥤ Type v}
variable {A : Type u} [CommRing A] [Algebra R A] (M : Submonoid A)
/-- The map `Spec A[1/b] ⟶ Spec A[1/a]` over `Spec R`, through `Spec A`, for `a ≤ b`. -/
def awayOver {a b : DivIndex M} (hab : a ≤ b) :
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away b.val))) ≫
      (Spec.map (CommRingCat.ofHom (algebraMap R A)) : Spec (CommRingCat.of A) ⟶ Spec R)) ⟶
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away a.val))) ≫
      (Spec.map (CommRingCat.ofHom (algebraMap R A)) : Spec (CommRingCat.of A) ⟶ Spec R)) :=
  Over.homMk (Spec.map (CommRingCat.ofHom (awayMap (show a.val ∣ b.val from hab)))) (by
    change _ ≫ _ ≫ _ = _ ≫ _
    simp only [← Spec.map_comp]
    congr 1
    ext x
    simp)

lemma awayOver_comp {a b : DivIndex M} (hab : a ≤ b) :
    awayOver M hab ≫ (towerIso A (Localization.Away a.val)).hom ≫
      homR (IsScalarTower.toAlgHom R A (Localization.Away a.val)) =
    (towerIso A (Localization.Away b.val)).hom ≫
      homR (IsScalarTower.toAlgHom R A (Localization.Away b.val)) := by
  ext1
  change Spec.map (CommRingCat.ofHom (awayMap (show a.val ∣ b.val from hab))) ≫ 𝟙 _ ≫
      Spec.map (CommRingCat.ofHom
        (IsScalarTower.toAlgHom R A (Localization.Away a.val)).toRingHom) =
    𝟙 _ ≫ Spec.map (CommRingCat.ofHom
      (IsScalarTower.toAlgHom R A (Localization.Away b.val)).toRingHom)
  rw [Category.id_comp, Category.id_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext x
  exact awayMap_algebraMap (show a.val ∣ b.val from hab) x

variable (B : Type u) [CommRing B] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
  [IsLocalization M B]

/-- The map `A[1/a] → M⁻¹A`, `a ∈ M`, as an `R`-algebra map. -/
def toLocₐ (a : DivIndex M) : Localization.Away a.val →ₐ[R] B :=
  { toLoc M B a with
    commutes' := fun r => by
      change toLoc M B a (algebraMap R (Localization.Away a.val) r) = algebraMap R B r
      rw [IsScalarTower.algebraMap_apply R A (Localization.Away a.val),
        IsScalarTower.algebraMap_apply R A B, toLoc_algebraMap] }

@[simp]
lemma toLocₐ_apply (a : DivIndex M) (x : Localization.Away a.val) :
    toLocₐ (R := R) M B a x = toLoc M B a x := rfl

/-- The map `Spec B ⟶ Spec A[1/a]` over `Spec R`, through `Spec A`. -/
def toLocOver (a : DivIndex M) :
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫
      (Spec.map (CommRingCat.ofHom (algebraMap R A)) : Spec (CommRingCat.of A) ⟶ Spec R)) ⟶
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away a.val))) ≫
      (Spec.map (CommRingCat.ofHom (algebraMap R A)) : Spec (CommRingCat.of A) ⟶ Spec R)) :=
  Over.homMk (Spec.map (CommRingCat.ofHom (toLoc M B a))) (by
    change _ ≫ _ ≫ _ = _ ≫ _
    simp only [← Spec.map_comp]
    congr 1
    ext x
    simp)

/-- (F2) for a localization `B = M⁻¹A`: every element of `F(Spec B)` comes from some
`F(Spec A[1/a])`, `a ∈ M`. -/
lemma exists_away_of_isLocalization (hZ : ZariskiSheaf F) (h2 : FilteredColimits F)
    (ζ : F.obj (op (ovR R B))) :
    ∃ (a : DivIndex M) (ζ' : F.obj (op (ovR R (Localization.Away a.val)))),
      F.map (homR (toLocₐ M B a)).op ζ' = ζ := by
  obtain ⟨a, ζ'₀, hζ⟩ := exists_eq_of_isLocalization M B hZ h2
    (Spec.map (CommRingCat.ofHom (algebraMap R A)) : Spec (CommRingCat.of A) ⟶ Spec R)
    (F.map (towerIso A B).hom.op ζ)
  have hζ' : F.map (toLocOver M B a).op ζ'₀ = F.map (towerIso A B).hom.op ζ := hζ
  refine ⟨a, F.map (towerIso A (Localization.Away a.val)).inv.op ζ'₀, ?_⟩
  have hk : homR (toLocₐ (R := R) M B a) ≫ (towerIso A (Localization.Away a.val)).inv =
      (towerIso A B).inv ≫ toLocOver M B a := by
    ext1
    change Spec.map (CommRingCat.ofHom (toLocₐ (R := R) M B a).toRingHom) ≫ 𝟙 _ =
      𝟙 _ ≫ Spec.map (CommRingCat.ofHom (toLoc M B a))
    rw [Category.comp_id, Category.id_comp]
    rfl
  calc F.map (homR (toLocₐ M B a)).op (F.map (towerIso A (Localization.Away a.val)).inv.op ζ'₀)
      = F.map (homR (toLocₐ M B a) ≫ (towerIso A (Localization.Away a.val)).inv).op ζ'₀ := by
        rw [op_comp, Functor.map_comp_apply]
    _ = F.map ((towerIso A B).inv ≫ toLocOver M B a).op ζ'₀ := by rw [hk]
    _ = F.map (towerIso A B).inv.op (F.map (toLocOver M B a).op ζ'₀) := by
        rw [op_comp, Functor.map_comp_apply]
    _ = ζ := by
        rw [hζ', ← Functor.map_comp_apply, ← op_comp, Iso.inv_hom_id, op_id,
          Functor.map_id_apply]

lemma toLocOver_comp (a : DivIndex M) :
    toLocOver M B a ≫ (towerIso A (Localization.Away a.val)).hom ≫
      homR (IsScalarTower.toAlgHom R A (Localization.Away a.val)) =
    (towerIso A B).hom ≫ homR (IsScalarTower.toAlgHom R A B) := by
  ext1
  change Spec.map (CommRingCat.ofHom (toLoc M B a)) ≫ 𝟙 _ ≫
      Spec.map (CommRingCat.ofHom
        (IsScalarTower.toAlgHom R A (Localization.Away a.val)).toRingHom) =
    𝟙 _ ≫ Spec.map (CommRingCat.ofHom (IsScalarTower.toAlgHom R A B).toRingHom)
  rw [Category.id_comp, Category.id_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext x
  exact toLoc_algebraMap M B a x

omit [Algebra R B] [IsScalarTower R A B] [IsLocalization M B] in
/-- Restriction from `Spec A` to `Spec A[1/a]`, as an element over `Spec A`. -/
def resAway {F : (Over (Spec R))ᵒᵖ ⥤ Type v} (a : DivIndex M) (ζ : F.obj (op (ovR R A))) :
    F.obj (op (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away a.val))) ≫
      (Spec.map (CommRingCat.ofHom (algebraMap R A)) : Spec (CommRingCat.of A) ⟶ Spec R)))) :=
  F.map (towerIso A (Localization.Away a.val)).hom.op
    (F.map (homR (IsScalarTower.toAlgHom R A (Localization.Away a.val))).op ζ)

lemma map_toLocOver_resAway (a : DivIndex M) (ζ : F.obj (op (ovR R A))) :
    F.map (toLocOver M B a).op (resAway M a ζ) =
      F.map (towerIso A B).hom.op (F.map (homR (IsScalarTower.toAlgHom R A B)).op ζ) := by
  rw [resAway, ← Functor.map_comp_apply, ← Functor.map_comp_apply, ← Functor.map_comp_apply,
    ← op_comp, ← op_comp, ← op_comp, Category.assoc, toLocOver_comp]

omit [Algebra R B] [IsScalarTower R A B] [IsLocalization M B] in
lemma map_awayOver_resAway {a b : DivIndex M} (hab : a ≤ b) (ζ : F.obj (op (ovR R A))) :
    F.map (awayOver M hab).op (resAway M a ζ) =
      F.map (towerIso A (Localization.Away b.val)).hom.op
        (F.map (homR (IsScalarTower.toAlgHom R A (Localization.Away b.val))).op ζ) := by
  rw [resAway, ← Functor.map_comp_apply, ← Functor.map_comp_apply, ← Functor.map_comp_apply,
    ← op_comp, ← op_comp, ← op_comp, Category.assoc, awayOver_comp]

/-- (F2) for a localization `B = M⁻¹A`: two elements of `F(Spec A)` with the same image in
`F(Spec B)` have the same image in some `F(Spec A[1/a])`, `a ∈ M`. -/
lemma exists_away_eq_of_eq (hZ : ZariskiSheaf F) (h2 : FilteredColimits F)
    (ζ₁ ζ₂ : F.obj (op (ovR R A)))
    (heq : F.map (homR (IsScalarTower.toAlgHom R A B)).op ζ₁ =
      F.map (homR (IsScalarTower.toAlgHom R A B)).op ζ₂) :
    ∃ a : DivIndex M,
      F.map (homR (IsScalarTower.toAlgHom R A (Localization.Away a.val))).op ζ₁ =
        F.map (homR (IsScalarTower.toAlgHom R A (Localization.Away a.val))).op ζ₂ := by
  obtain ⟨a₀⟩ : Nonempty (DivIndex M) := inferInstance
  have heq₀ : F.map (toLocOver M B a₀).op (resAway M a₀ ζ₁) =
      F.map (toLocOver M B a₀).op (resAway M a₀ ζ₂) := by
    rw [map_toLocOver_resAway, map_toLocOver_resAway, heq]
  obtain ⟨b, hab, hb⟩ := exists_eq_of_isLocalization_of_eq M B hZ h2
    (Spec.map (CommRingCat.ofHom (algebraMap R A)) : Spec (CommRingCat.of A) ⟶ Spec R) a₀ _ _
    heq₀
  refine ⟨b, ?_⟩
  have hb' : F.map (awayOver M (leOfHom hab)).op (resAway M a₀ ζ₁) =
      F.map (awayOver M (leOfHom hab)).op (resAway M a₀ ζ₂) := hb
  rw [map_awayOver_resAway, map_awayOver_resAway] at hb'
  have hinj := congrArg (F.map (towerIso A (Localization.Away b.val)).inv.op) hb'
  simpa only [← Functor.map_comp_apply, ← op_comp, Iso.inv_hom_id_assoc] using hinj

end F2

section Field

variable {F : (Over (Spec R))ᵒᵖ ⥤ Type v}

/-- With (F1b), restriction from a field `K` to a field `L` over it is injective. -/
lemma map_injective_of_field (hF : FaithfullyFlatSheaf F) {K L : Type u} [Field K]
    [Algebra R K] [Field L] (f : Spec (CommRingCat.of L) ⟶ Spec R) (z : Over.mk f ⟶ ovR R K) :
    Function.Injective (F.map z.op) := by
  intro a b hab
  have hflat : Flat z.left := by
    rw [← Spec.map_preimage z.left, HasRingHomProperty.Spec_iff (P := @Flat)]
    let := (Spec.preimage z.left).hom.toAlgebra
    show Module.Flat K L
    infer_instance
  have hsurj : Surjective z.left := ⟨fun x =>
    ⟨Nonempty.some (inferInstance : Nonempty (PrimeSpectrum L)), eq_of_isArtinianRing _ _⟩⟩
  have : IsAffine (Over.mk f).left := inferInstanceAs (IsAffine (Spec (CommRingCat.of L)))
  have : IsAffine (ovR R K).left := inferInstanceAs (IsAffine (Spec (CommRingCat.of K)))
  have hqc : QuasiCompact z.left := inferInstance
  exact (hF z hflat hsurj hqc).isSeparatedFor.ext fun Y g hg => by
    cases hg
    exact hab

end Field

section Away

variable {A : Type u} [CommRing A] [Algebra R A]

/-- For `a ∣ b`, the `R`-algebra map `A[1/a] → A[1/b]`. -/
def awayMapₐ {a b : A} (h : a ∣ b) : Localization.Away a →ₐ[R] Localization.Away b :=
  { awayMap h with
    commutes' := fun r => by
      change awayMap h (algebraMap R (Localization.Away a) r) = algebraMap R _ r
      rw [IsScalarTower.algebraMap_apply R A (Localization.Away a),
        IsScalarTower.algebraMap_apply R A (Localization.Away b), awayMap_algebraMap] }

@[simp]
lemma awayMapₐ_apply {a b : A} (h : a ∣ b) (x : Localization.Away a) :
    awayMapₐ (R := R) h x = awayMap h x := rfl

lemma awayMapₐ_comp_toAlgHom {a b : A} (h : a ∣ b) :
    (awayMapₐ (R := R) h).comp (IsScalarTower.toAlgHom R A (Localization.Away a)) =
      IsScalarTower.toAlgHom R A (Localization.Away b) := by
  ext x
  exact awayMap_algebraMap h x

lemma homR_awayMapₐ_comp {a b : A} (h : a ∣ b) :
    homR (awayMapₐ (R := R) h) ≫ homR (IsScalarTower.toAlgHom R A (Localization.Away a)) =
      homR (IsScalarTower.toAlgHom R A (Localization.Away b)) := by
  rw [← homR_comp, awayMapₐ_comp_toAlgHom]

instance isOpenImmersion_homR_awayMapₐ {a b : A} (h : a ∣ b) :
    IsOpenImmersion (homR (awayMapₐ (R := R) h)).left := by
  have h₁ : (homR (awayMapₐ (R := R) h)).left ≫
      Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away a))) =
        Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away b))) := by
    rw [homR_left, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext x
    exact awayMap_algebraMap h x
  have : IsOpenImmersion ((homR (awayMapₐ (R := R) h)).left ≫
      Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away a)))) := by
    rw [h₁]
    infer_instance
  exact IsOpenImmersion.of_comp _
    (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away a))))

end Away

end Charts

end Langlands.AlgebraicGeometry.UnramifiedFunctor
