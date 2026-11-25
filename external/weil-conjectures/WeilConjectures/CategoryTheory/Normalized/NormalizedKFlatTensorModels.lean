/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.K.KFlatBifunctorTensorHom
import all WeilConjectures.CategoryTheory.K.KFlatBifunctorTensorHom
import all WeilConjectures.WeilSheaf.SixFunctors.DerivedWeilTensorOperations

/-! # Evaluation-normalized models of K-flat total tensor

Source: Stacks 0A96, 08J9 and 06YN.
(blueprint: lem-sf-normalized-kflat-tensor-models).
-/

@[expose] public section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory
variable {A : Type u} [Category.{v} A] [Abelian A]
  [HasCountableProducts A] [HasCountableCoproducts A] [HasDerivedCategory.{v} A]
variable (F : A ⥤ A ⥤ A) [F.flip.Additive] [∀ P, (F.flip.obj P).Additive]
  (H₀ : Aᵒᵖ ⥤ A ⥤ A) [H₀.Additive] [∀ P, (H₀.obj P).Additive]
  (a : ∀ T, F.obj T ⊣ H₀.obj (op T))
  (H : (DerivedCategory A)ᵒᵖ × DerivedCategory A ⥤ DerivedCategory A)
  (R : AlgebraicGeometry.ProEtaleWeilSheaf.NativeHomRepresentatives H₀ H)
  (S : WeilConjectures.CoefficientClosedStructure H)
  (KFlat : CochainComplex A ℤ → Prop)

/-- The signed componentwise evaluation fixes the model, rather than just its naturality.
Source: Stacks 0A96 and 08J9, tensor--Hom on complexes and K-injective localization.
(blueprint: lem-sf-normalized-kflat-tensor-models). -/
def KFlatTensorModelNormalization
    (model : ∀ P T : CochainComplex A ℤ, KFlat P → KFlat T →
      (S.tensor.obj (DerivedCategory.Q.obj P, DerivedCategory.Q.obj T) ≅
        DerivedCategory.Q.obj ((F.flip.map₂CochainComplex.obj P).obj T))) : Prop :=
  ∀ (P T I : CochainComplex A ℤ) (hP : KFlat P) (hT : KFlat T)
    (hI : I.IsKInjective) (φ : P ⟶ CochainComplex.bifunctorHomObj H₀ T I),
    ∃ ψ : (F.flip.map₂CochainComplex.obj P).obj T ⟶ I,
      (∀ (p q n : ℤ) (hpq : p + q = n),
        HomologicalComplex.ιMapBifunctor P T F.flip (.up ℤ) p q n hpq ≫ ψ.f n =
          (p * q).negOnePow •
            ((F.obj (T.X q)).map (φ.f p ≫
                CochainComplex.bifunctorHomπ H₀ T I p q n (by omega)) ≫
              (a (T.X q)).counit.app (I.X n))) ∧
      (model P T hP hT).hom ≫ DerivedCategory.Q.map ψ =
        (S.transpose (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj T)
          (DerivedCategory.Q.obj I)).symm
            (DerivedCategory.Q.map φ ≫ (R.model T I hI).inv)

/-- Normalized total tensor models, including their evaluation and naturality equations.
Source: Stacks 0A96, 08J9, 06YN and the representative tensor--Hom construction.
(blueprint: lem-sf-normalized-kflat-tensor-models).

Proof: the parametrized adjunction gives the isomorphism of Hom complexes. Its
unflipped degree-zero uncurry is unsigned. Exchange the two total directions to
put the left degree first; on bidegree (p,q) the exchange has coefficient
(-1)^(pq), giving precisely the displayed formula. For K-flat T and K-injective I,
Hom(T,I) is K-injective, by transposing maps from an acyclic complex and using
acyclicity of its tensor with T. Hence localization identifies both Hom sets
with the corresponding homotopy Hom sets. Compose with R.model. Represent an
arbitrary derived target by a K-injective complex and transport this bijection
through its representing isomorphism. Its naturality follows by representing
maps between K-injectives by actual complex maps and using R.naturality.
Yoneda and the fixed closed adjunction S determine a unique representing
isomorphism. The identity and inverse identity maps prove its inverse laws.
The same Hom bijection gives naturality in P,T by injectivity of transposition.
For a given φ its componentwise uncurry is a genuine complex map ψ; the total
coproduct universal property gives its displayed summand formula. The definition
of the Hom bijection then gives the displayed localized equality. This fixes
all scalar and Weil-action ambiguities: for any other normalized model, every
map to a K-injective target has the same composite, and the Yoneda test forces
equality. Zero complexes, empty sites and unbounded totals use the same proof. -/
theorem normalizedKFlatTensorModels [Abelian.HasKInjectiveResolutions A]
    (adj : F ⊣₂ H₀)
    (hflat : ∀ T, KFlat T →
      ∀ {P P' : CochainComplex A ℤ} (f : P ⟶ P'), QuasiIso f →
        QuasiIso ((F.flip.map₂CochainComplex.flip.obj T).map f)) :
    ∃ model : ∀ P T : CochainComplex A ℤ, KFlat P → KFlat T →
      (S.tensor.obj (DerivedCategory.Q.obj P, DerivedCategory.Q.obj T) ≅
        DerivedCategory.Q.obj ((F.flip.map₂CochainComplex.obj P).obj T)),
      (∀ (P P' T T' : CochainComplex A ℤ)
        (hP : KFlat P) (hP' : KFlat P') (hT : KFlat T) (hT' : KFlat T')
        (f : P ⟶ P') (g : T ⟶ T'),
        S.tensor.map (Prod.mkHom (DerivedCategory.Q.map f) (DerivedCategory.Q.map g)) ≫
            (model P' T' hP' hT').hom =
          (model P T hP hT).hom ≫ DerivedCategory.Q.map
            ((F.flip.map₂CochainComplex.map f).app T ≫
              (F.flip.map₂CochainComplex.obj P').map g)) ∧
      KFlatTensorModelNormalization F H₀ adj.adj H R S KFlat model := by
  classical
  let : F.Additive := by
    constructor
    intro A B f g
    apply NatTrans.ext
    funext P
    exact (F.flip.obj P).map_add
  let (A : A) : (F.obj A).Additive := by
    constructor
    intro B C f g
    exact congrArg (fun t ↦ t.app A) (F.flip.map_add (f := f) (g := g))
  let flat (T : CochainComplex A ℤ) (hT : KFlat T)
      {P P' : CochainComplex A ℤ} (f : P ⟶ P') (h : QuasiIso f) :
      QuasiIso (HomologicalComplex.mapBifunctorMap (𝟙 T) f F (.up ℤ)) := by
    have hf := hflat T hT f h
    have he := HomologicalComplex.mapBifunctorFlipIso_hom_naturality
      (𝟙 T) f F (.up ℤ)
    have hf' : QuasiIso (HomologicalComplex.mapBifunctorMap f (𝟙 T) F.flip (.up ℤ)) := hf
    have : QuasiIso
        (HomologicalComplex.mapBifunctorMap f (𝟙 T) F.flip (.up ℤ) ≫
          (HomologicalComplex.mapBifunctorFlipIso T P' F (.up ℤ)).hom) := by
      infer_instance
    rw [he] at this
    exact (quasiIso_iff_comp_left
      (HomologicalComplex.mapBifunctorFlipIso T P F (.up ℤ)).hom _).1 this
  let d (P T : CochainComplex A ℤ) (hT : KFlat T)
      (I : CochainComplex A ℤ) [I.IsKInjective] :
      (DerivedCategory.Q.obj ((F.flip.map₂CochainComplex.obj P).obj T) ⟶
        DerivedCategory.Q.obj I) ≃
        (DerivedCategory.Q.obj P ⟶ H.obj (op (DerivedCategory.Q.obj T),
          DerivedCategory.Q.obj I)) :=
    DerivedNativeTensorProof.derivedEquiv adj H R T P I (flat T hT)
  let J := DerivedCategory.kInjectiveRep (B := A)
  let j := DerivedCategory.kInjectiveRepIso (B := A)
  let e (P T : CochainComplex A ℤ) (hT : KFlat T) (Z : DerivedCategory A) :
      (DerivedCategory.Q.obj ((F.flip.map₂CochainComplex.obj P).obj T) ⟶ Z) ≃
        (DerivedCategory.Q.obj P ⟶ H.obj (op (DerivedCategory.Q.obj T), Z)) :=
    (j Z).homToEquiv.trans ((d P T hT (J Z)).trans
      (H.mapIso ((Iso.refl (op (DerivedCategory.Q.obj T))).prod (j Z))).symm.homToEquiv)
  have he (P T : CochainComplex A ℤ) (hT : KFlat T) (Z : DerivedCategory A)
      (a : DerivedCategory.Q.obj ((F.flip.map₂CochainComplex.obj P).obj T) ⟶ Z) :
      e P T hT Z a =
        d P T hT (J Z) (a ≫ (j Z).hom) ≫
          H.map (Prod.mkHom (𝟙 _) (j Z).inv) := rfl
  have hn : ∀ P T (hT : KFlat T) (Z Z' : DerivedCategory A)
      (a : DerivedCategory.Q.obj ((F.flip.map₂CochainComplex.obj P).obj T) ⟶ Z)
      (b : Z ⟶ Z'), e P T hT Z' (a ≫ b) =
        e P T hT Z a ≫ H.map (Prod.mkHom (𝟙 _) b) := by
    intro P T hT Z Z' a b
    let b' := (j Z).inv ≫ b ≫ (j Z').hom
    obtain ⟨b₀, hb₀⟩ := (DerivedNativeTensorProof.qHomEquiv (J Z) (J Z')).surjective b'
    obtain ⟨b₁, hb₁⟩ := (HomotopyCategory.quotient A (.up ℤ)).map_surjective b₀
    have hb : DerivedCategory.Q.map b₁ = b' := by
      rw [← DerivedNativeTensorProof.qHomEquiv_map, hb₁, hb₀]
    have h := DerivedNativeTensorProof.derivedEquiv_naturality adj H R
      T T P P (J Z) (J Z') (flat T hT) (flat T hT)
      (𝟙 T) (𝟙 P) b₁ (a ≫ (j Z).hom)
    simp only [DerivedNativeTensorProof.total_map_id, Functor.map_id,
      Category.id_comp, op_id, Functor.map_id] at h
    rw [hb] at h
    have hh : (a ≫ (j Z).hom) ≫ b' = (a ≫ b) ≫ (j Z').hom := by
      simp [b', Category.assoc]
    rw [hh] at h
    rw [he P T hT Z' (a ≫ b), he P T hT Z a]
    change d P T hT (J Z') ((a ≫ b) ≫ (j Z').hom) =
      d P T hT (J Z) (a ≫ (j Z).hom) ≫
        H.map (Prod.mkHom (𝟙 _) b') at h
    rw [h]
    simp only [Category.assoc, ← H.map_comp]
    congr 1
    apply congrArg H.map
    ext <;> simp [b', Category.assoc]
  have hf : ∀ P P' T T' (hT : KFlat T) (hT' : KFlat T')
      (f : P ⟶ P') (g : T ⟶ T') (Z : DerivedCategory A)
      (a : DerivedCategory.Q.obj ((F.flip.map₂CochainComplex.obj P').obj T') ⟶ Z),
      e P T hT Z (DerivedCategory.Q.map
          ((F.flip.map₂CochainComplex.map f).app T ≫
            (F.flip.map₂CochainComplex.obj P').map g) ≫ a) =
        DerivedCategory.Q.map f ≫ e P' T' hT' Z a ≫
          H.map (Prod.mkHom (DerivedCategory.Q.map g).op (𝟙 Z)) := by
    intro P P' T T' hT hT' f g Z a
    have h := DerivedNativeTensorProof.derivedEquiv_naturality adj H R
      T' T P' P (J Z) (J Z) (flat T' hT') (flat T hT)
      g f (𝟙 _) (a ≫ (j Z).hom)
    simp only [Functor.map_id, Category.comp_id] at h
    have hm : (F.flip.map₂CochainComplex.map f).app T ≫
        (F.flip.map₂CochainComplex.obj P').map g =
        HomologicalComplex.mapBifunctorMap f g F.flip (.up ℤ) := by
      change HomologicalComplex.mapBifunctorMap f (𝟙 T) F.flip (.up ℤ) ≫
        HomologicalComplex.mapBifunctorMap (𝟙 P') g F.flip (.up ℤ) = _
      simp only [HomologicalComplex.mapBifunctorMap, Functor.map_id, NatTrans.id_app,
        Category.id_comp, Category.comp_id, ← HomologicalComplex₂.total.map_comp]
    rw [he P T hT Z _, he P' T' hT' Z a, hm]
    simp only [Category.assoc]
    change d P T hT (J Z)
        (DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap f g F.flip (.up ℤ)) ≫
          (a ≫ (j Z).hom)) ≫ H.map (Prod.mkHom (𝟙 _) (j Z).inv) = _
    change d P T hT (J Z)
        (DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap f g F.flip (.up ℤ)) ≫
          (a ≫ (j Z).hom)) =
      DerivedCategory.Q.map f ≫ d P' T' hT' (J Z) (a ≫ (j Z).hom) ≫
        H.map (Prod.mkHom (DerivedCategory.Q.map g).op (𝟙 _)) at h
    rw [h]
    simp only [Category.assoc, ← H.map_comp]
    congr 2
    apply congrArg H.map
    ext <;> simp
  -- Yoneda identifies the normalized Hom bijection with the fixed closed tensor.
  let c (P T : CochainComplex A ℤ) (hT : KFlat T) (Z : DerivedCategory A) :=
    (e P T hT Z).trans (S.transpose (DerivedCategory.Q.obj P)
      (DerivedCategory.Q.obj T) Z).symm
  have hc (P T : CochainComplex A ℤ) (hT : KFlat T) (Z Z' : DerivedCategory A)
      (a : DerivedCategory.Q.obj ((F.flip.map₂CochainComplex.obj P).obj T) ⟶ Z)
      (b : Z ⟶ Z') : c P T hT Z' (a ≫ b) = c P T hT Z a ≫ b := by
    change (S.transpose _ _ _).symm (e P T hT Z' (a ≫ b)) = _
    rw [hn P T hT Z Z' a b]
    exact (S.adjunction (DerivedCategory.Q.obj T)).homEquiv_naturality_right_symm _ _
  let i (P T : CochainComplex A ℤ) (hT : KFlat T) :=
    DerivedNativeTensorProof.isoOfHomEquiv (c P T hT) (hc P T hT)
  refine ⟨fun P T _ hT ↦ i P T hT, ?_, ?_⟩
  · intro P P' T T' hP hP' hT hT' f g
    have hi := hc P T hT (DerivedCategory.Q.obj ((F.flip.map₂CochainComplex.obj P).obj T))
      (DerivedCategory.Q.obj ((F.flip.map₂CochainComplex.obj P').obj T')) (𝟙 _)
      (DerivedCategory.Q.map ((F.flip.map₂CochainComplex.map f).app T ≫
        (F.flip.map₂CochainComplex.obj P').map g))
    rw [Category.id_comp] at hi
    change _ = c P T hT _ (𝟙 _) ≫ _
    rw [← hi]
    change S.tensor.map (Prod.mkHom (DerivedCategory.Q.map f) (DerivedCategory.Q.map g)) ≫
      (S.transpose _ _ _).symm (e P' T' hT' _ (𝟙 _)) =
        (S.transpose _ _ _).symm (e P T hT _ _)
    rw [← Category.comp_id (DerivedCategory.Q.map
      ((F.flip.map₂CochainComplex.map f).app T ≫
        (F.flip.map₂CochainComplex.obj P').map g)),
      hf P P' T T' hT hT' f g _ (𝟙 _)]
    exact (DerivedNativeTensorProof.uncurry_both S _ _ _ _ _
      (DerivedCategory.Q.map f) (DerivedCategory.Q.map g) _).symm
  · intro P T I hP hT hI φ
    let := hI
    let ψ₀ := (DerivedNativeTensorProof.internalHomEquiv adj T I P).symm φ
    let ψ := (HomologicalComplex.mapBifunctorFlipIso T P F (.up ℤ)).hom ≫ ψ₀
    refine ⟨ψ, ?_, ?_⟩
    · intro p q n hpq
      have hqp : q + p = n := by omega
      have hu := DerivedNativeTensorProof.internalHomEquiv_f_π adj ψ₀ p q n hqp
      rw [show DerivedNativeTensorProof.internalHomEquiv adj T I P ψ₀ = φ from
        Equiv.apply_symm_apply _ _] at hu
      have hv := congrArg ((adj.adj (T.X q)).homEquiv (P.X p) (I.X n)).symm hu
      simp only [DerivedNativeTensorProof.curry, Adjunction.homAddEquiv_apply,
        Equiv.symm_apply_apply] at hv
      dsimp only [ψ, HomologicalComplex.comp_f]
      rw [← Category.assoc, HomologicalComplex.ι_mapBifunctorFlipIso_hom,
        Linear.units_smul_comp]
      change (q * p).negOnePow •
        (HomologicalComplex.ιMapBifunctor T P F (.up ℤ) q p n hqp ≫ ψ₀.f n) = _
      rw [← hv, Adjunction.homEquiv_counit, mul_comm q p]
    · have hvalue : e P T hT (DerivedCategory.Q.obj I) (DerivedCategory.Q.map ψ) =
          DerivedCategory.Q.map φ ≫ (R.model T I hI).inv := by
        let b' := (j (DerivedCategory.Q.obj I)).hom
        obtain ⟨b₀, hb₀⟩ :=
          (DerivedNativeTensorProof.qHomEquiv I (J (DerivedCategory.Q.obj I))).surjective b'
        obtain ⟨b₁, hb₁⟩ := (HomotopyCategory.quotient A (.up ℤ)).map_surjective b₀
        have hb : DerivedCategory.Q.map b₁ = b' := by
          rw [← DerivedNativeTensorProof.qHomEquiv_map, hb₁, hb₀]
        have ht := DerivedNativeTensorProof.derivedEquiv_naturality adj H R
          T T P P I (J (DerivedCategory.Q.obj I)) (flat T hT) (flat T hT)
          (𝟙 T) (𝟙 P) b₁ (DerivedCategory.Q.map ψ)
        simp only [DerivedNativeTensorProof.total_map_id, Functor.map_id,
          Category.id_comp, op_id] at ht
        rw [hb] at ht
        rw [he P T hT (DerivedCategory.Q.obj I) (DerivedCategory.Q.map ψ)]
        change d P T hT (J (DerivedCategory.Q.obj I))
          (DerivedCategory.Q.map ψ ≫ b') ≫ _ = _
        rw [show d P T hT (J (DerivedCategory.Q.obj I))
            (DerivedCategory.Q.map ψ ≫ b') =
          d P T hT I (DerivedCategory.Q.map ψ) ≫
            H.map (X := (op (DerivedCategory.Q.obj T), DerivedCategory.Q.obj I))
              (Y := (op (DerivedCategory.Q.obj T),
                DerivedCategory.Q.obj (J (DerivedCategory.Q.obj I)))) (𝟙 _, b') from ht]
        simp only [Category.assoc, ← H.map_comp]
        have hid : Prod.mkHom (𝟙 (op (DerivedCategory.Q.obj T))) b' ≫
            Prod.mkHom (𝟙 _) (j (DerivedCategory.Q.obj I)).inv = 𝟙 _ := by
          ext <;> simp [b']
        rw [hid, H.map_id, Category.comp_id]
        change DerivedNativeTensorProof.derivedEquiv adj H R T P I (flat T hT)
          (DerivedCategory.Q.map ψ) = _
        rw [DerivedNativeTensorProof.derivedEquiv_map]
        congr 2
        dsimp only [ψ, ψ₀]
        rw [Iso.inv_hom_id_assoc, Equiv.apply_symm_apply]
      have hi := hc P T hT
        (DerivedCategory.Q.obj ((F.flip.map₂CochainComplex.obj P).obj T))
        (DerivedCategory.Q.obj I) (𝟙 _) (DerivedCategory.Q.map ψ)
      rw [Category.id_comp] at hi
      change c P T hT _ (𝟙 _) ≫ DerivedCategory.Q.map ψ = _
      rw [← hi]
      change (S.transpose _ _ _).symm (e P T hT _ (DerivedCategory.Q.map ψ)) = _
      rw [hvalue]

end CategoryTheory
