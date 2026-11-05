import Langlands.GroupScheme.SplitExistence.Generation
import Langlands.GroupScheme.SplitExistence.ExtPoints
import Langlands.GroupScheme.SplitExistence.TitsFinal
import Langlands.GroupScheme.Dynamic.GeneralLinear
import Langlands.GroupScheme.Rational.LeviFactorization

/-! # Geometric points of the Chevalley group, the regular cocharacter, and factorizations

* Transport of the abstract subgroups `T`, `U_j`, `Γ`, `U⁺`, `B` along ring homomorphisms.
* The identification of `K`-valued points of `GL_n` with `GL_n(K)` for a field extension `K`.
* The cocharacter `λ : 𝔾ₘ → D(X)` attached to the functional `ℓ`, whose image in `GL_n` is the
  diagonal cocharacter `t ↦ diag(t ^ ℓ(wt c))`.
* Factorization of homomorphisms through closed subgroups. -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SplitExistence

/-- A homomorphism whose underlying morphism factors through a closed subgroup factors through it
as a homomorphism. -/
theorem exists_hom_factor {S : Scheme.{u}} {H G M : GroupScheme S} (j : M ⟶ G)
    (hj : IsClosedSubgroup j) (f : H ⟶ G) (hf : FactorsThrough f.hom.hom j) :
    ∃ g : H ⟶ M, g ≫ j = f := by
  have : IsClosedImmersion j.hom.hom.left := hj
  have hrep : (SubgroupFunctor.range j).IsRepresentedBy j := ⟨Over.mono_of_mono_left _, rfl⟩
  have hle : SubgroupFunctor.range f ≤ SubgroupFunctor.range j := by
    rintro T x ⟨y, rfl⟩
    change T ⟶ H.X at y
    obtain ⟨c, hc⟩ := hf
    refine ⟨y ≫ c, ?_⟩
    change (y ≫ c) ≫ j.hom.hom = y ≫ f.hom.hom
    rw [Category.assoc, hc]
  exact ⟨hrep.factorHom f hle, hrep.factorHom_comp f hle⟩

/-- `GL_n` of isomorphic rings. -/
def glMapEquiv {n : Type*} [Fintype n] [DecidableEq n] {A B : Type*} [CommRing A] [CommRing B]
    (e : A ≃+* B) : GL n A ≃* GL n B where
  toFun := Matrix.GeneralLinearGroup.map e.toRingHom
  invFun := Matrix.GeneralLinearGroup.map e.symm.toRingHom
  left_inv g := by
    ext i j
    simp
  right_inv g := by
    ext i j
    simp
  map_mul' g h := map_mul _ g h

namespace ChevalleyData

variable {J X Y : Type u} [AddCommGroup X] [AddCommGroup Y] {P : RootDatum J X Y} {b : P.Base}
  (D : ChevalleyData P b)

section Transport

variable {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B)

theorem map_torusSub_le :
    (D.torusSub A).map (Matrix.GeneralLinearGroup.map f) ≤ D.torusSub B := by
  rintro _ ⟨g, ⟨χ, rfl⟩, rfl⟩
  exact ⟨_, (D.torusHom_map f χ).symm⟩

theorem map_rootSub_le (j : J) :
    (D.rootSub A j).map (Matrix.GeneralLinearGroup.map f) ≤ D.rootSub B j := by
  rintro _ ⟨g, hg, rfl⟩
  obtain ⟨s, rfl⟩ := mem_rootSub.1 hg
  rw [D.x_map]
  exact x_mem_rootSub j _

theorem map_rootsSub_le (S : Set J) :
    (D.rootsSub A S).map (Matrix.GeneralLinearGroup.map f) ≤ D.rootsSub B S := by
  rw [rootsSub, MonoidHom.map_closure]
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨g, hg, rfl⟩
  obtain ⟨j, hj, hg⟩ := Set.mem_iUnion₂.1 hg
  exact rootSub_le_rootsSub hj (D.map_rootSub_le f j ⟨g, hg, rfl⟩)

theorem map_chevSub_le :
    (D.chevSub A).map (Matrix.GeneralLinearGroup.map f) ≤ D.chevSub B := by
  rw [chevSub, Subgroup.map_sup]
  exact sup_le_sup (D.map_torusSub_le f) (D.map_rootsSub_le f _)

theorem map_borelSub_le :
    (D.borelSub A).map (Matrix.GeneralLinearGroup.map f) ≤ D.borelSub B := by
  rw [borelSub, Subgroup.map_sup]
  exact sup_le_sup (D.map_torusSub_le f) (D.map_rootsSub_le f _)

theorem mem_chevSub_iff_of_equiv (e : A ≃+* B) {g : GL (Fin D.n) A} :
    g ∈ D.chevSub A ↔ glMapEquiv e g ∈ D.chevSub B := by
  constructor
  · intro hg
    exact D.map_chevSub_le e.toRingHom ⟨g, hg, rfl⟩
  · intro hg
    have h := D.map_chevSub_le e.symm.toRingHom ⟨_, hg, rfl⟩
    rwa [show Matrix.GeneralLinearGroup.map e.symm.toRingHom (glMapEquiv e g) = g from
      (glMapEquiv e).symm_apply_apply g] at h

theorem mem_borelSub_iff_of_equiv (e : A ≃+* B) {g : GL (Fin D.n) A} :
    g ∈ D.borelSub A ↔ glMapEquiv e g ∈ D.borelSub B := by
  constructor
  · intro hg
    exact D.map_borelSub_le e.toRingHom ⟨g, hg, rfl⟩
  · intro hg
    have h := D.map_borelSub_le e.symm.toRingHom ⟨_, hg, rfl⟩
    rwa [show Matrix.GeneralLinearGroup.map e.symm.toRingHom (glMapEquiv e g) = g from
      (glMapEquiv e).symm_apply_apply g] at h

end Transport

/-- The weights `c ↦ ℓ(wt c)` of the regular cocharacter on the basis. -/
def ellWeights : Fin D.n → ℤ := fun c => D.ℓ (D.wt c)

/-- The character-valued map `t ↦ (x ↦ t ^ ℓ(x))`: the cocharacter `λ` on points. -/
def ellChar (R : Type u) [CommRing R] : Rˣ →* (Multiplicative X →* Rˣ) where
  toFun t :=
    { toFun := fun x => t ^ D.ℓ (Multiplicative.toAdd x)
      map_one' := by simp
      map_mul' := fun x y => by simp [zpow_add] }
  map_one' := by
    ext
    simp
  map_mul' s t := by
    ext
    simp [mul_zpow]

theorem torusHom_ellChar {R : Type u} [CommRing R] (t : Rˣ) :
    D.torusHom (D.ellChar R t) = GeneralLinear.diagonalUnits R D.ellWeights t := by
  ext c d
  simp [coe_torusHom, GeneralLinear.coe_diagonalUnits, ellChar, ellWeights]

theorem ellChar_map {R R' : Type u} [CommRing R] [CommRing R'] (f : R →+* R') (t : Rˣ) :
    (Units.map f.toMonoidHom).comp (D.ellChar R t) = D.ellChar R' (Units.map f.toMonoidHom t) := by
  ext x
  simp [ellChar]

variable (k : Type u) [Field k]

/-- The cocharacter `λ` on points over a test scheme. -/
def cocharPoints (T : Over (Spec (CommRingCat.of k))) :
    (T ⟶ (Gm (Spec (CommRingCat.of k))).X) →* (T ⟶ (Tk (X := X) k).toGrp.X) :=
  (torusPointsEquiv k T).symm.toMonoidHom.comp
    ((D.ellChar Γ(T.left, ⊤)).comp (Gm.pointsEquiv _ T).toMonoidHom)

theorem torusPointsEquiv_cocharPoints (T : Over (Spec (CommRingCat.of k)))
    (x : T ⟶ (Gm (Spec (CommRingCat.of k))).X) :
    torusPointsEquiv k T (D.cocharPoints k T x) = D.ellChar _ (Gm.pointsEquiv _ T x) :=
  MulEquiv.apply_symm_apply _ _

theorem cocharPoints_naturality {T T' : Over (Spec (CommRingCat.of k))} (a : T' ⟶ T)
    (x : T ⟶ (Gm (Spec (CommRingCat.of k))).X) :
    D.cocharPoints k T' (a ≫ x) = a ≫ D.cocharPoints k T x := by
  apply (torusPointsEquiv k T').injective
  rw [torusPointsEquiv_cocharPoints, Gm.pointsEquiv_naturality, ← D.ellChar_map,
    ← torusPointsEquiv_cocharPoints]
  rfl

/-- The cocharacter `λ : 𝔾ₘ → D(X)` with `χ(λ(t)) = t ^ ℓ(χ)`. -/
def cochar : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ (Tk (X := X) k).toGrp :=
  homOfPoints (D.cocharPoints k) fun a x => D.cocharPoints_naturality k a x

theorem cochar_comp_torusToGL :
    D.cochar k ≫ D.torusToGL k =
      GeneralLinear.diagonalCocharacter (Fin D.n) (CommRingCat.of k) D.ellWeights := by
  refine hom_ext_points fun T x => ?_
  apply (GeneralLinear.pointsEquiv (Fin D.n) (CommRingCat.of k) T).injective
  rw [Grp.comp_hom_hom, ← Category.assoc, pointsEquiv_torusToGL, cochar, comp_homOfPoints,
    torusPointsEquiv_cocharPoints, torusHom_ellChar,
    GeneralLinear.pointsEquiv_diagonalCocharacter]

section ExtPoints

variable (K : Type u) [Field K] [Algebra k K]

/-- The global sections of `Spec K`, identified with `K`. -/
def specRingEquiv : Γ((extPoint (k := k) K).left, ⊤) ≃+* K :=
  (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv

/-- The `K`-valued points of `GL_n` over `k`, as `GL_n(K)`. -/
def glExt : (extPoint (k := k) K ⟶ (D.GLk k).X) ≃* GL (Fin D.n) K :=
  (GeneralLinear.pointsEquiv (Fin D.n) (CommRingCat.of k) (extPoint K)).trans
    (glMapEquiv (specRingEquiv k K))

theorem mem_chevPoints_iff_glExt {x : extPoint (k := k) K ⟶ (D.GLk k).X} :
    x ∈ D.chevPoints k (extPoint K) ↔ D.glExt k K x ∈ D.chevSub K :=
  D.mem_chevSub_iff_of_equiv (specRingEquiv k K)

end ExtPoints

end ChevalleyData

end Langlands.GroupScheme.SplitExistence
