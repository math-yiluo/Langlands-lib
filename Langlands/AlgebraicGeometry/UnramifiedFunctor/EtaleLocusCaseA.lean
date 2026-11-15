import Langlands.AlgebraicGeometry.UnramifiedFunctor.EtaleLocusGen

/-! # The étale locus near a point lying over a prime that is not nilpotent

Let `y` be a point of `Spec (R'/𝔍)` at which `ξ` is infinitesimally étale and let `𝔭` be the
prime of `R` below `y`, with `I = 𝔭 R'`. If `𝔭` is not contained in the nilradical, every
`𝔭^(n+1)` is nonzero and the hypothesis on closed subschemes gives levels
`R' → R'/I^(n+1)`. For points `w` with `I ⊆ P_w` we use the local data
`O_w/(𝔍 + I^(n+1))O_w` and the condition `VanN n w`: `𝔍` vanishes in the stalk at level `n`.
With the Artin–Rees constant `c` of `𝔍 ⊆ R'` for `I`, `VanN n w` implies `VanN (n+1) w`
for `n ≥ c` (`van_succ`); the set of `w` with `VanN c w` is relatively open in `V(I)`
(`exists_open_van`). Together these give an open neighbourhood `V` of `y` whose points
specializing `y` lie in the étale locus (`exists_open_of_not_le_nilradical`). -/

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite IsLocalRing

noncomputable section

namespace Langlands.AlgebraicGeometry.UnramifiedFunctor

namespace EtaleLocus

section Germ

/-- The set of points where the germ of a section vanishes is open. -/
lemma isOpen_germ_eq_zero {X : Scheme.{u}} (U : X.Opens) (s : Γ(X, U)) :
    IsOpen {x : X | ∃ hx : x ∈ U, X.presheaf.germ U x hx s = 0} := by
  rw [isOpen_iff_forall_mem_open]
  rintro x ⟨hx, h⟩
  obtain ⟨V, i, hxV, hV⟩ := X.toRingedSpace.exists_res_eq_zero_of_germ_eq_zero U s ⟨x, hx⟩ h
  refine ⟨V, fun x' hx' => ⟨i.le hx', ?_⟩, V.2, hxV⟩
  rw [← X.presheaf.germ_res_apply i x' hx', hV, map_zero]

/-- The set of points where an element of `D` vanishes in the stalk is open. -/
lemma isOpen_structMap_eq_zero {X : Scheme.{u}} {D : CommRingCat.{u}} (q : X ⟶ Spec D)
    (d₀ : D) : IsOpen {x : X | (structMap q x).hom d₀ = 0} := by
  have h : {x : X | (structMap q x).hom d₀ = 0} = {x : X | ∃ hx : x ∈ q ⁻¹ᵁ ⊤,
      X.presheaf.germ (q ⁻¹ᵁ ⊤) x hx (q.app ⊤ ((Scheme.ΓSpecIso D).inv.hom d₀)) = 0} := by
    ext x
    have e : (structMap q x).hom d₀ = X.presheaf.germ (q ⁻¹ᵁ ⊤) x trivial
        (q.app ⊤ ((Scheme.ΓSpecIso D).inv.hom d₀)) :=
      Scheme.Hom.germ_stalkMap_apply q ⊤ x trivial _
    simp only [Set.mem_ofPred_eq, e]
    exact ⟨fun h => ⟨trivial, h⟩, fun ⟨_, h⟩ => h⟩
  rw [h]
  exact isOpen_germ_eq_zero _ _

end Germ

variable {R : CommRingCat.{u}} {F : (Over (Spec R))ᵒᵖ ⥤ Type v}
  {R' : Type u} [CommRing R'] [Algebra R R'] {𝔍 : Ideal R'}

namespace LocalDatum

variable {D : Type u} [CommRing D] {ρ : R' →+* D} {w : Spec (CommRingCat.of (R' ⧸ 𝔍))}
  {L : Type u} [CommRing L] [IsLocalRing L] (d : LocalDatum R 𝔍 ρ w L)
  (ξ : F.obj (op (chart R R' 𝔍))) (Lv : Level F ρ)

/-- An element over `T` restricting to the image of `ξ` in `F(Spec L)` gives a morphism
`T ⟶ X` restricting to the point of `X` given by `ξ`. -/
lemma left_of_map_eq {T : Over (Spec R)} (t : T.left ⟶ Spec (CommRingCat.of D))
    (ht : t ≫ levelMap R ρ = T.hom) (z : F.obj (op T)) (k : Over.mk d.f ⟶ T)
    (hkt : k.left ≫ t = Spec.map (CommRingCat.ofHom d.δ)) (hz : F.map k.op z = d.ζ ξ) :
    k.left ≫ ((Charts.elemEquiv (levelMap R ρ) Lv.e T t ht).symm z).left =
      (d.mor ξ Lv).left := by
  have hza : z = Charts.elemEquiv (levelMap R ρ) Lv.e T t ht
      ((Charts.elemEquiv (levelMap R ρ) Lv.e T t ht).symm z) := (Equiv.apply_symm_apply _ _).symm
  have ht₁ : (k.left ≫ t) ≫ levelMap R ρ = (Over.mk d.f).hom := by
    rw [Category.assoc, ht]
    exact Over.w k
  have e1 := elemEquiv_naturality' (levelMap R ρ) Lv.e k (k.left ≫ t) t ht₁ ht rfl
    ((Charts.elemEquiv (levelMap R ρ) Lv.e T t ht).symm z)
  rw [← hza, hz] at e1
  have e2 : d.ζ ξ = Charts.elemEquiv _ Lv.e (Over.mk d.f) _ d.hT (d.mor ξ Lv) :=
    (Equiv.apply_symm_apply _ _).symm
  exact left_eq_of_elemEquiv_eq _ Lv.e ht₁ d.hT hkt _ _ (e1.symm.trans e2)

/-- A morphism `Spec C ⟶ X` restricting along a local map `C → L` to the point given by `ξ`
sends the closed point to that point. -/
lemma pt_eq_of {C : Type u} [CommRing C] [IsLocalRing C] (h : Spec (CommRingCat.of C) ⟶ Lv.X)
    (π : C →+* L) [IsLocalHom π] (hπ : Spec.map (CommRingCat.ofHom π) ≫ h = (d.mor ξ Lv).left) :
    h (closedPoint (CommRingCat.of C)) = d.pt ξ Lv := by
  have : IsLocalHom (CommRingCat.ofHom π).hom := ‹_›
  have h5 : Spec.map (CommRingCat.ofHom π) (closedPoint (CommRingCat.of L)) =
      closedPoint (CommRingCat.of C) := Spec_closedPoint
  exact (congrArg (fun y => h y) h5.symm).trans ((Scheme.Hom.comp_apply _ _ _).symm.trans
    (congrArg (fun g => g (closedPoint (CommRingCat.of L))) hπ))

end LocalDatum

section CaseA

variable [IsNoetherianRing R'] (I : Ideal R')

variable (𝔍) in
/-- The local ring `O_w/(𝔍 + I^(n+1))O_w`. -/
abbrev Ln (n : ℕ) (w : Spec (CommRingCat.of (R' ⧸ 𝔍))) : Type u :=
  Ow 𝔍 w ⧸ (𝔍 ⊔ I ^ (n + 1)).map (algebraMap R' (Ow 𝔍 w))

instance (n : ℕ) (w : Spec (CommRingCat.of (R' ⧸ 𝔍))) [Fact (I ≤ primeOf 𝔍 w)] :
    IsLocalRing (Ln 𝔍 I n w) :=
  isLocalRing_std ((Ideal.pow_le_self n.succ_ne_zero).trans Fact.out) le_rfl

variable (R 𝔍) in
/-- The local datum `O_w/(𝔍 + I^(n+1))O_w` at `w` for the level `R' → R'/I^(n+1)`. -/
def nDatum (n : ℕ) (w : Spec (CommRingCat.of (R' ⧸ 𝔍))) [Fact (I ≤ primeOf 𝔍 w)] :
    LocalDatum R 𝔍 (Ideal.Quotient.mk (I ^ (n + 1))) w (Ln 𝔍 I n w) :=
  stdDatum (ρ := Ideal.Quotient.mk (I ^ (n + 1))) (w := w)
    (fun _ _ _ _ h => Ideal.Quotient.ringHom_ext h) (I ^ (n + 1)) Ideal.mk_ker.ge
    ((𝔍 ⊔ I ^ (n + 1)).map (algebraMap R' (Ow 𝔍 w))) (Ideal.map_mono le_sup_left) le_rfl
    (Ideal.quotientMap _ (algebraMap R' (Ow 𝔍 w))
      (Ideal.map_le_iff_le_comap.1 (Ideal.map_mono le_sup_right)))
    (Ideal.quotientMap_comp_mk _)
    (Spec.map (CommRingCat.ofHom (algebraMap R' (Ln 𝔍 I n w))) ≫ baseMap R R')
    (by rw [specMap_ofHom_comp]; rfl)

variable (𝔍) in
/-- `𝔍` vanishes in the stalk at level `n` at `w`. -/
def VanN (Lvs : ∀ n : ℕ, Level F (Ideal.Quotient.mk (I ^ (n + 1))))
    (ξ : F.obj (op (chart R R' 𝔍))) (n : ℕ) (w : Spec (CommRingCat.of (R' ⧸ 𝔍)))
    [Fact (I ≤ primeOf 𝔍 w)] : Prop :=
  ∀ j ∈ 𝔍, ((nDatum R 𝔍 I n w).θ ξ (Lvs n)).hom (Ideal.Quotient.mk _ j) = 0

end CaseA

end EtaleLocus

end Langlands.AlgebraicGeometry.UnramifiedFunctor
