import Langlands.GroupScheme.SL2CentralExtension.TorsionDensity
import Langlands.GroupScheme.Reductive.UnitPowerFppfCover
import Langlands.GroupScheme.Reductive.RelativeDerivedInputs

/-! # Natural bilinear pairings of units vanish in separated commutative groups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SL2CentralExtension

/-- A natural, separately multiplicative family of pairings of global units. -/
structure UnitPairing {S : Scheme.{u}} (Z : CommGroupScheme S) where
  app : ∀ T : Over S, Γ(T.left, ⊤)ˣ →* Γ(T.left, ⊤)ˣ →* (T ⟶ Z.X)
  naturality : ∀ {T U : Over S} (k : U ⟶ T) (s t : Γ(T.left, ⊤)ˣ),
    k ≫ app T s t = app U (Units.map k.left.appTop.hom.toMonoidHom s)
      (Units.map k.left.appTop.hom.toMonoidHom t)

/-- Equality of morphisms can be checked after a single surjective fppf map. -/
theorem hom_ext_of_surjective_fppf {S : Scheme.{u}} {T U Y : Over S} (j : U ⟶ T)
    [Flat j.left] [Surjective j.left] [LocallyOfFinitePresentation j.left]
    (f g : T ⟶ Y) (h : j ≫ f = j ≫ g) : f = g := by
  let 𝒰 : Scheme.Cover.{u}
      (Scheme.precoverage (@Flat ⊓ @LocallyOfFinitePresentation)) T.left :=
    Scheme.Cover.mkOfCovers PUnit (fun _ => U.left) (fun _ => j.left)
      (fun t => by
        obtain ⟨v, hv⟩ := (Scheme.Hom.surjective j.left) t
        exact ⟨PUnit.unit, v, hv⟩)
      (fun _ => ⟨inferInstance, inferInstance⟩)
  let := RelativeDerived.effectiveEpiFamily_fppfCover 𝒰
  apply Over.OverMorphism.ext
  apply EffectiveEpiFamily.hom_ext 𝒰.X 𝒰.f
  intro i
  exact congrArg CommaMorphism.left h

namespace UnitPairing

variable {S : Scheme.{u}} {Z : CommGroupScheme S} (p : UnitPairing Z)

/-- A finite-order input annihilates a natural unit pairing on any affine test. -/
theorem torsion_eq_one_affine {V : Over S} [IsAffine V.left] (s t : Γ(V.left, ⊤)ˣ)
    (n : ℕ) (hs : s ^ (n + 1) = 1) : p.app V s t = 1 := by
  obtain ⟨W, k, hW, hflat, hsurj, hfp, r, hr⟩ :=
    UnitPowerExtension.exists_roots_test V (n + 1) (Nat.succ_ne_zero n)
      (m := 1) (fun _ => t)
  let : Flat k.left := hflat
  let : Surjective k.left := hsurj
  let : LocallyOfFinitePresentation k.left := hfp
  apply hom_ext_of_surjective_fppf k
  rw [MonObj.comp_one, p.naturality, ← hr 0]
  have hs' : (Units.map k.left.appTop.hom.toMonoidHom s) ^ (n + 1) = 1 := by
    rw [← map_pow, hs, map_one]
  calc
    p.app W (Units.map k.left.appTop.hom.toMonoidHom s) (r 0 ^ (n + 1)) =
        p.app W ((Units.map k.left.appTop.hom.toMonoidHom s) ^ (n + 1)) (r 0) := by
      simp only [map_pow, MonoidHom.pow_apply]
    _ = 1 := by rw [hs', map_one, MonoidHom.one_apply]

/-- A finite-order input annihilates a natural unit pairing on every test. -/
theorem torsion_eq_one {V : Over S} (s t : Γ(V.left, ⊤)ˣ)
    (n : ℕ) (hs : s ^ (n + 1) = 1) : p.app V s t = 1 := by
  apply Over.OverMorphism.ext
  apply V.left.affineCover.hom_ext
  intro i
  let U : Over S := Over.mk (V.left.affineCover.f i ≫ V.hom)
  let k : U ⟶ V := Over.homMk (V.left.affineCover.f i) rfl
  have : IsAffine U.left := by
    change IsAffine (V.left.affineCover.X i)
    infer_instance
  have hs' : (Units.map k.left.appTop.hom.toMonoidHom s) ^ (n + 1) = 1 := by
    rw [← map_pow, hs, map_one]
  have he : k ≫ p.app V s t = k ≫ (1 : V ⟶ Z.X) := by
    rw [MonObj.comp_one, p.naturality]
    exact p.torsion_eq_one_affine _ _ n hs'
  exact congrArg CommaMorphism.left he

/-- Every natural unit pairing into a separated commutative group scheme is
identically the identity point. -/
theorem eq_one [IsSeparated Z.X.hom] (V : Over S) (s t : Γ(V.left, ⊤)ˣ) :
    p.app V s t = 1 := by
  let F : ∀ ⦃W : Over S⦄ (_ : W ⟶ V), Γ(W.left, ⊤)ˣ → (W ⟶ Z.X) :=
    fun W g a => p.app W a (Units.map g.left.appTop.hom.toMonoidHom t)
  let F' : ∀ ⦃W : Over S⦄ (_ : W ⟶ V), Γ(W.left, ⊤)ˣ → (W ⟶ Z.X) :=
    fun _ _ _ => 1
  have hF : ∀ ⦃W U : Over S⦄ (g : W ⟶ V) (k : U ⟶ W) (a : Γ(W.left, ⊤)ˣ),
      k ≫ F g a = F (k ≫ g) (Units.map k.left.appTop.hom.toMonoidHom a) := by
    intro W U g k a
    change k ≫ p.app W a _ = p.app U _ _
    rw [p.naturality]
    rfl
  have hF' : ∀ ⦃W U : Over S⦄ (g : W ⟶ V) (k : U ⟶ W) (a : Γ(W.left, ⊤)ˣ),
      k ≫ F' g a = F' (k ≫ g) (Units.map k.left.appTop.hom.toMonoidHom a) := by
    intro W U g k a
    exact MonObj.comp_one k
  have hroot : ∀ ⦃W : Over S⦄ (g : W ⟶ V) (a : Γ(W.left, ⊤)ˣ) (n : ℕ),
      a ^ (n + 1) = 1 → F g a = F' g a := by
    intro W g a n ha
    exact p.torsion_eq_one a _ n ha
  have he := units_natural_ext F F' hF hF' hroot (𝟙 V) s
  change p.app V s ((Units.map (MonoidHom.id Γ(V.left, ⊤))) t) = 1 at he
  simpa only [Units.map_id, MonoidHom.id_apply] using he

end UnitPairing

end Langlands.GroupScheme.SL2CentralExtension
