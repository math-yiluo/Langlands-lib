import Langlands.GroupScheme.Reductive.AffineRootLieDerivative
import Langlands.GroupScheme.Reductive.LocalSimpleRootPowerRigidity
import Langlands.GroupScheme.Reductive.RelativeTorusConjugationRigidity
import Langlands.GroupScheme.Reductive.GlobalSplitRootParametrization
import Langlands.GroupScheme.Reductive.AffinePinnedIsomorphismTheoremStatement

/-! # Uniqueness in the pinned Isomorphism Theorem over an affine base -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme

open LocalSplitCell LocalSplitRootBaseChange

section LocalToGlobal

variable {R : Type u} [CommRing R] {G H : GroupScheme (Spec (CommRingCat.of R))}

/-- Homomorphisms into a group scheme with affine total space are determined by
their base changes to all local commutative algebras. -/
theorem hom_ext_of_localBaseChange [IsAffine H.X.left] {f F : G ⟶ H}
    (h : ∀ (A : Type u) [CommRing A] [IsLocalRing A] [Algebra R A],
      (baseChange (algebraBaseMap R A)).map f = (baseChange (algebraBaseMap R A)).map F) :
    f = F := by
  apply Grp.hom_ext
  apply Over.OverMorphism.ext
  apply CellGluing.hom_ext_of_localRingPoints
  intro A _ _ q
  let s := q ≫ G.X.hom
  let φ := Spec.preimage s
  let : Algebra R A := φ.hom.toAlgebra
  have hs : algebraBaseMap R A = s := by
    change Spec.map (CommRingCat.ofHom φ.hom) = s
    rw [CommRingCat.ofHom_hom, Spec.map_preimage]
  let e : Over.mk s ≅ fieldPoint R A := Over.isoMk (Iso.refl _) (by
    change 𝟙 _ ≫ 𝟙 _ ≫ algebraBaseMap R A = s
    rw [Category.id_comp, Category.id_comp, hs])
  let z : fieldPoint R A ⟶ G.X := e.inv ≫ Over.homMk q rfl
  let x := (baseChangePointsEquiv (algebraBaseMap R A) G (𝟙_ _)).symm z
  have hx := congrArg
    (fun y => baseChangePointsEquiv (algebraBaseMap R A) H (𝟙_ _) (x ≫ y.hom.hom)) (h A)
  simp only [baseChangePointsEquiv_comp, x, MulEquiv.apply_symm_apply] at hx
  exact congrArg CommaMorphism.left (congrArg (e.hom ≫ ·) hx)

end LocalToGlobal

section BaseChange

variable {R : Type u} [CommRing R] {G : GroupScheme (Spec (CommRingCat.of R))}
  {I : Type u} [Fintype I] (A : Type u) [CommRing A] [Algebra R A]

/-- Base change preserves a torus inclusion fixed by an endomorphism. -/
theorem baseChangeHom_comp_of_comp_eq (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G)
    {σ : G ⟶ G} (hσ : i ≫ σ = i) :
    splitTorus.baseChangeHom (K := A) G I i ≫ (baseChange (algebraBaseMap R A)).map σ =
      splitTorus.baseChangeHom (K := A) G I i := by
  rw [splitTorus.baseChangeHom, Category.assoc, ← Functor.map_comp, hσ]

/-- The normalized base-changed torus inclusion of a closed torus is closed. -/
theorem isClosedSubgroup_baseChangeHom (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G)
    (hi : IsClosedSubgroup i) : IsClosedSubgroup (splitTorus.baseChangeHom (K := A) G I i) := by
  let : IsClosedImmersion
      ((baseChange (algebraBaseMap R A)).map i).hom.hom.left :=
    hi.baseChange _
  change IsClosedImmersion
    ((splitTorus.baseChangeIso (algebraBaseMap R A) I).inv.hom.hom.left ≫
      ((baseChange (algebraBaseMap R A)).map i).hom.hom.left)
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in
  infer_instance

end BaseChange

section Rigidity

variable {R : Type u} [CommRing R] {G : GroupScheme (Spec (CommRingCat.of R))}
  [IsAffineHom G.X.hom] {I : Type u} [Fintype I] [DecidableEq I] {J : Type u}

omit [DecidableEq I] in
/-- An automorphism fixing the torus and the simple root lines fixes the chosen
global parametrizations of the simple roots. -/
theorem simpleRoot_comp_eq_of_fixes (hG : IsReductive G)
    (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G)
    (hmax : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i)
    {P : RootDatum J (I → ℤ) (I → ℤ)} (hP : IsFibrewiseRootDatumOf I G i P)
    (hfree : ∀ α : J, Nonempty
      (splitTorus.exponentWeightSpace I G i (P.root α) ≃ₗ[CommRingCat.of R] CommRingCat.of R))
    (b : P.Base) (σ : G ≅ G) (hσ : i ≫ σ.hom = i)
    (hX : ∀ a ∈ b.support, ∀ Y ∈ splitTorus.exponentWeightSpace I G i (P.root a),
      Lie.targetMapLinear σ.hom (CommRingCat.of R) Y = Y)
    (a : J) (ha : a ∈ b.support) :
    LocalRootGroup.rootParametrizationsOfFreeWeights i hG hmax hP hfree a ≫ σ.hom =
      LocalRootGroup.rootParametrizationsOfFreeWeights i hG hmax hP hfree a :=
  (LocalRootGroup.isRootParametrization_rootParametrizationsOfFreeWeights i hG hmax hP hfree
    a).comp_eq_of_fixes_weightSpace (P.ne_zero a) σ hσ (hX a ha)

/-- Over every local algebra, the base change of such an automorphism is the
identity. -/
theorem baseChange_map_eq_id_of_fixes (hG : IsReductive G)
    (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G) (hi : IsClosedSubgroup i)
    (hmax : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i)
    {P : RootDatum J (I → ℤ) (I → ℤ)} (hP : IsFibrewiseRootDatumOf I G i P)
    (hfree : ∀ α : J, Nonempty
      (splitTorus.exponentWeightSpace I G i (P.root α) ≃ₗ[CommRingCat.of R] CommRingCat.of R))
    (b : P.Base) (σ : G ≅ G) (hσ : i ≫ σ.hom = i)
    (hX : ∀ a ∈ b.support, ∀ Y ∈ splitTorus.exponentWeightSpace I G i (P.root a),
      Lie.targetMapLinear σ.hom (CommRingCat.of R) Y = Y)
    (A : Type u) [CommRing A] [IsLocalRing A] [Algebra R A] :
    (baseChange (algebraBaseMap R A)).map σ.hom = 𝟙 _ := by
  classical
  let : Smooth G.X.hom := hG.smooth
  let : IsAffineHom ((baseChange (algebraBaseMap R A)).obj G).X.hom :=
    inferInstanceAs (IsAffineHom (pullback.snd G.X.hom (algebraBaseMap R A)))
  let iA := splitTorus.baseChangeHom (K := A) G I i
  let σA := (baseChange (algebraBaseMap R A)).mapIso σ
  have hGA := hG.baseChange (algebraBaseMap R A)
  have hiA : IsClosedSubgroup iA := isClosedSubgroup_baseChangeHom A i hi
  have hmaxA : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) iA :=
    splitTorus.isFibrewiseMaximalTorus_baseChangeHom I G i hmax
  have hPA : IsFibrewiseRootDatumOf I _ iA P := hP.baseChange_implicit (A := A)
  have hσA : iA ≫ σA.hom = iA := baseChangeHom_comp_of_comp_eq A i hσ
  let U := simpleRootFamilyLocal hGA iA hiA hmaxA hPA b
  have hU := simpleRootFamilyLocal_spec hGA iA hiA hmaxA hPA b
  have hpos : ∀ a ∈ b.support, U a ≫ σA.hom = U a := by
    intro a ha
    have hu := LocalRootGroup.isRootParametrization_rootParametrizationsOfFreeWeights
      i hG hmax hP hfree a
    have huA := isRootParametrization_baseChangeRoot A i (P.root a) _ hu
    obtain ⟨c, hc⟩ := (hU.1 a ha).1.exists_scalar_of_ne_zero huA (P.ne_zero a)
    change U a ≫ (baseChange (algebraBaseMap R A)).map σ.hom = U a
    rw [show U a = _ from hc, Category.assoc, baseChangeRoot, Category.assoc,
      ← CategoryTheory.Functor.map_comp,
      simpleRoot_comp_eq_of_fixes hG i hmax hP hfree b σ hσ hX a ha]
  have hneg : ∀ a ∈ b.support, ∃ d : A,
      U (P.reflectionPerm a a) ≫ σA.hom = scaleHom d ≫ U (P.reflectionPerm a a) := by
    intro a ha
    have h2 := (hU.1 a ha).2
    exact (h2.comp_iso σA hσA).exists_scalar_of_ne_zero h2 (P.ne_zero _)
  choose! d hd using hneg
  exact hom_ext_of_chosenSimpleRootPowerFormulas hGA hGA iA iA hiA hiA hmaxA hmaxA hPA hPA
    b b id (fun a ha => ha) σA.hom (𝟙 _) (𝟙 _)
    (by rw [hσA, Category.id_comp]) (by rw [Category.comp_id, Category.id_comp])
    (fun _ => 1) d (fun _ => 1) (fun _ => 1) (fun _ _ => Nat.one_pos)
    (fun a ha => ⟨fun Z x => by
        rw [← rootPoint_comp, hpos a ha, Units.val_one, map_one, one_mul, pow_one]; rfl,
      fun Z x => by
        rw [← rootPoint_comp, hd a ha, rootPoint_scaleHom, pow_one]; rfl⟩)
    (fun a ha => ⟨fun Z x => by
        rw [Grp.id_hom_hom, Category.comp_id, Units.val_one, map_one, one_mul, pow_one]; rfl,
      fun Z x => by
        rw [Grp.id_hom_hom, Category.comp_id, map_one, one_mul, pow_one]; rfl⟩)

/-- **Rigidity of pinned automorphisms over an affine base.** An automorphism of
a split reductive group scheme over `Spec R` that is the identity on the split
maximal torus and whose differential fixes every simple root line is the
identity. -/
theorem iso_eq_refl_of_fixes (hG : IsReductive G)
    (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G) (hi : IsClosedSubgroup i)
    (hmax : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i)
    {P : RootDatum J (I → ℤ) (I → ℤ)} (hP : IsFibrewiseRootDatumOf I G i P)
    (hfree : ∀ α : J, Nonempty
      (splitTorus.exponentWeightSpace I G i (P.root α) ≃ₗ[CommRingCat.of R] CommRingCat.of R))
    (b : P.Base) (σ : G ≅ G) (hσ : i ≫ σ.hom = i)
    (hX : ∀ a ∈ b.support, ∀ Y ∈ splitTorus.exponentWeightSpace I G i (P.root a),
      Lie.targetMapLinear σ.hom (CommRingCat.of R) Y = Y) :
    σ = Iso.refl G := by
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  ext1
  apply hom_ext_of_localBaseChange
  intro A _ _ _
  rw [baseChange_map_eq_id_of_fixes hG i hi hmax hP hfree b σ hσ hX A, Iso.refl_hom,
    CategoryTheory.Functor.map_id]

/-- Pinned automorphism rigidity, with the simple root lines given by
trivializations whose generators are fixed by the differential. -/
theorem iso_eq_refl_of_fixes_pinning (hG : IsReductive G)
    (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G) (hi : IsClosedSubgroup i)
    (hmax : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i)
    {P : RootDatum J (I → ℤ) (I → ℤ)} (hP : IsFibrewiseRootDatumOf I G i P)
    (hfree : ∀ α : J, Nonempty
      (splitTorus.exponentWeightSpace I G i (P.root α) ≃ₗ[CommRingCat.of R] CommRingCat.of R))
    (b : P.Base)
    (X : ∀ a : b.support, CommRingCat.of R ≃ₗ[CommRingCat.of R]
      splitTorus.exponentWeightSpace I G i (P.root a))
    (σ : G ≅ G) (hσ : i ≫ σ.hom = i)
    (hX : ∀ a : b.support,
      Lie.targetMapLinear σ.hom (CommRingCat.of R) (X a 1).val = (X a 1).val) :
    σ = Iso.refl G :=
  iso_eq_refl_of_fixes hG i hi hmax hP hfree b σ hσ
    (fun a ha => fixes_weightSpace_of_fixes_generator σ (X ⟨a, ha⟩) (hX ⟨a, ha⟩))

end Rigidity

section Torus

variable {S : Scheme.{u}} {I I' : Type u} [Fintype I] [Fintype I']

/-- A homomorphism of split tori is determined by its pullback of characters. -/
theorem splitTorus_hom_eq_of_characters (w : (I' → ℤ) → (I → ℤ))
    (τ τ' : splitTorus S I ⟶ splitTorus S I')
    (hτ : ∀ (U : Over S) (x : U ⟶ (splitTorus S I).X) (m : I' → ℤ),
      ∏ j', splitTorus.pointsEquiv I' U (x ≫ τ.hom.hom) j' ^ m j' =
        ∏ j, splitTorus.pointsEquiv I U x j ^ w m j)
    (hτ' : ∀ (U : Over S) (x : U ⟶ (splitTorus S I).X) (m : I' → ℤ),
      ∏ j', splitTorus.pointsEquiv I' U (x ≫ τ'.hom.hom) j' ^ m j' =
        ∏ j, splitTorus.pointsEquiv I U x j ^ w m j) :
    τ = τ' := by
  classical
  have key : ∀ (U : Over S) (x : U ⟶ (splitTorus S I).X),
      splitTorus.pointsEquiv I' U (x ≫ τ.hom.hom) =
        splitTorus.pointsEquiv I' U (x ≫ τ'.hom.hom) := by
    intro U x
    funext j'
    have h := (hτ U x (Pi.single j' 1)).trans (hτ' U x (Pi.single j' 1)).symm
    have hs : ∀ y : I' → (Γ(U.left, ⊤))ˣ,
        ∏ k, y k ^ (Pi.single j' (1 : ℤ) : I' → ℤ) k = y j' := by
      intro y
      rw [Fintype.prod_eq_single j' (fun k hk => by rw [Pi.single_eq_of_ne hk, zpow_zero]),
        Pi.single_eq_same, zpow_one]
    rwa [hs, hs] at h
  apply Grp.hom_ext
  have h := (splitTorus.pointsEquiv I' _).injective (key _ (𝟙 _))
  rwa [Category.id_comp, Category.id_comp] at h

end Torus

section Pinned

/-- **Uniqueness in the pinned Isomorphism Theorem, with a common torus map.**
Two isomorphisms of split reductive group schemes over `Spec R` that restrict
to the same torus homomorphism and carry the source pinning vectors to the
same target pinning vectors are equal. -/
theorem affinePinned_hom_eq {R : Type u} [CommRing R]
    {G H : GroupScheme (Spec (CommRingCat.of R))} [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
    (hG : IsReductive G) {I I' : Type u} [Fintype I] [Fintype I']
    (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G)
    (i' : splitTorus (Spec (CommRingCat.of R)) I' ⟶ H)
    {J J' : Type u} {P : RootDatum J (I → ℤ) (I → ℤ)} {Q : RootDatum J' (I' → ℤ) (I' → ℤ)}
    (hi : IsClosedSubgroup i)
    (hmax : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i)
    (hP : IsFibrewiseRootDatumOf I G i P)
    (hfree : ∀ α : J, Nonempty
      (splitTorus.exponentWeightSpace I G i (P.root α) ≃ₗ[CommRingCat.of R] CommRingCat.of R))
    (b : P.Base) (b' : Q.Base)
    (X : ∀ a : b.support, CommRingCat.of R ≃ₗ[CommRingCat.of R]
      splitTorus.exponentWeightSpace I G i (P.root a))
    (Y : ∀ a' : b'.support, CommRingCat.of R ≃ₗ[CommRingCat.of R]
      splitTorus.exponentWeightSpace I' H i' (Q.root a'))
    (f : RootPairing.Equiv Q P)
    (hf : ∀ j' : J', j' ∈ b'.support ↔ f.indexEquiv j' ∈ b.support)
    (φ ψ : G ≅ H)
    (τ : splitTorus (Spec (CommRingCat.of R)) I ⟶ splitTorus (Spec (CommRingCat.of R)) I')
    (hφ : i ≫ φ.hom = τ ≫ i') (hψ : i ≫ ψ.hom = τ ≫ i')
    (hφX : ∀ a' : b'.support,
      Lie.targetMapLinear φ.hom (CommRingCat.of R)
          (X ⟨f.indexEquiv a', (hf a').mp a'.property⟩ 1).val = (Y a' 1).val)
    (hψX : ∀ a' : b'.support,
      Lie.targetMapLinear ψ.hom (CommRingCat.of R)
          (X ⟨f.indexEquiv a', (hf a').mp a'.property⟩ 1).val = (Y a' 1).val) :
    φ = ψ := by
  classical
  let σ : G ≅ G := ψ ≪≫ φ.symm
  have hσ : i ≫ σ.hom = i := by
    change i ≫ ψ.hom ≫ φ.inv = i
    rw [← Category.assoc, hψ, ← hφ, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hgen : ∀ a : b.support,
      Lie.targetMapLinear σ.hom (CommRingCat.of R) (X a 1).val = (X a 1).val := by
    intro a
    obtain ⟨a', rfl⟩ : ∃ a' : b'.support,
        (⟨f.indexEquiv a', (hf a').mp a'.property⟩ : b.support) = a :=
      ⟨⟨f.indexEquiv.symm a, (hf _).mpr (by simp)⟩,
        Subtype.ext (by simp)⟩
    change Lie.targetMapLinear (ψ.hom ≫ φ.inv) (CommRingCat.of R) _ = _
    rw [Lie.targetMapLinear_comp, LinearMap.comp_apply, hψX a', ← hφX a',
      ← LinearMap.comp_apply, ← Lie.targetMapLinear_comp, Iso.hom_inv_id,
      Lie.targetMapLinear_id, LinearMap.id_apply]
  have h := congrArg Iso.hom (iso_eq_refl_of_fixes_pinning hG i hi hmax hP hfree b X σ hσ hgen)
  change ψ.hom ≫ φ.inv = 𝟙 G at h
  ext1
  rw [((Iso.comp_inv_eq φ).mp h), Category.id_comp]

/-- **Uniqueness in the pinned Isomorphism Theorem over an affine base**, in the
shape of `AffinePinnedIsomorphismTheoremStatement`: two isomorphisms satisfying
its torus and pinning compatibilities are equal. -/
theorem affinePinnedIsomorphism_unique (R : Type u) [CommRing R]
    (G H : GroupScheme (Spec (CommRingCat.of R)))
    (hG : IsReductive G) (hH : IsReductive H)
    (I I' : Type u) [Fintype I] [Fintype I']
    (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G)
    (i' : splitTorus (Spec (CommRingCat.of R)) I' ⟶ H)
    (J J' : Type u) (P : RootDatum J (I → ℤ) (I → ℤ)) (Q : RootDatum J' (I' → ℤ) (I' → ℤ)) :
    haveI := hG.isAffineHom
    haveI := hH.isAffineHom
    IsClosedSubgroup i →
    IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme (Spec (CommRingCat.of R)) I) i →
    IsFibrewiseRootDatumOf I G i P →
    (∀ α : J, Nonempty
      (splitTorus.exponentWeightSpace I G i (P.root α) ≃ₗ[CommRingCat.of R] CommRingCat.of R)) →
    ∀ (b : P.Base) (b' : Q.Base)
      (X : ∀ a : b.support, CommRingCat.of R ≃ₗ[CommRingCat.of R]
        splitTorus.exponentWeightSpace I G i (P.root a))
      (Y : ∀ a' : b'.support, CommRingCat.of R ≃ₗ[CommRingCat.of R]
        splitTorus.exponentWeightSpace I' H i' (Q.root a'))
      (f : RootPairing.Equiv Q P)
      (hf : ∀ j' : J', j' ∈ b'.support ↔ f.indexEquiv j' ∈ b.support)
      (φ ψ : G ≅ H),
      ((∃ τ : splitTorus (Spec (CommRingCat.of R)) I ≅
            splitTorus (Spec (CommRingCat.of R)) I',
          i ≫ φ.hom = τ.hom ≫ i' ∧
          ∀ (U : Over (Spec (CommRingCat.of R)))
            (x : U ⟶ (splitTorus (Spec (CommRingCat.of R)) I).X) (m : I' → ℤ),
            ∏ j', splitTorus.pointsEquiv I' U (x ≫ τ.hom.hom.hom) j' ^ m j' =
              ∏ j, splitTorus.pointsEquiv I U x j ^ f.weightMap m j) ∧
        ∀ a' : b'.support,
          Lie.targetMapLinear φ.hom (CommRingCat.of R)
              (X ⟨f.indexEquiv a', (hf a').mp a'.property⟩ 1).val =
            (Y a' 1).val) →
      ((∃ τ : splitTorus (Spec (CommRingCat.of R)) I ≅
            splitTorus (Spec (CommRingCat.of R)) I',
          i ≫ ψ.hom = τ.hom ≫ i' ∧
          ∀ (U : Over (Spec (CommRingCat.of R)))
            (x : U ⟶ (splitTorus (Spec (CommRingCat.of R)) I).X) (m : I' → ℤ),
            ∏ j', splitTorus.pointsEquiv I' U (x ≫ τ.hom.hom.hom) j' ^ m j' =
              ∏ j, splitTorus.pointsEquiv I U x j ^ f.weightMap m j) ∧
        ∀ a' : b'.support,
          Lie.targetMapLinear ψ.hom (CommRingCat.of R)
              (X ⟨f.indexEquiv a', (hf a').mp a'.property⟩ 1).val =
            (Y a' 1).val) →
      φ = ψ := by
  intro hi hmax hP hfree b b' X Y f hf φ ψ ⟨⟨τ, hφ, hτ⟩, hφX⟩ ⟨⟨τ', hψ, hτ'⟩, hψX⟩
  have := hG.isAffineHom
  have := hH.isAffineHom
  have hττ : τ.hom = τ'.hom := splitTorus_hom_eq_of_characters _ τ.hom τ'.hom hτ hτ'
  rw [hττ] at hφ
  exact affinePinned_hom_eq hG i i' hi hmax hP hfree b b' X Y f hf φ ψ τ'.hom hφ hψ hφX hψX

end Pinned

end Langlands.GroupScheme
