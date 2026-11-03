import Langlands.GroupScheme.Absolute.GeneralLinearSolvableStabilizerStatement
import Langlands.GroupScheme.GeneralLinearActionOfPoints
import Langlands.GroupScheme.Reductive.Basic
import Langlands.AbelianScheme.KernelBaseChange
import Langlands.LinearAlgebra.FullFlagSolvable
import Langlands.RingTheory.Grassmannian.FlagLocus
import Langlands.AnthropicFLT.Theorems.Thm_Module_Grassmannian_exists_scheme_represents_and_isClosedImmersion_toProjSpace
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_exists_isClosedImmersion_represents_of_forall_exists_ideal

/-! # `GL_N` acts on a proper scheme with solvable point stabilizers

The witness is the closed subscheme `Z` of the quotient Grassmannian
`G(rank N, Idx N → k)` cut out by the flag condition `FlagLocus.Stable`. Its points over a
`k`-algebra `A` are the stable points of `G(rank N, A ⊗[k] (Idx N → k); A)`, and `GL_N(A)` acts
on them by `FlagLocus.smul`. This action is natural in `A` and therefore comes from a scheme
action of `GL_N`. The scheme `Z` is proper, being closed in a closed subscheme of projective
space, and nonempty, since the standard flag is a rational point.

If a closed subgroup `H` fixes a rational point, then every point of `H` over the algebraic
closure `k̄` fixes the corresponding stable point over `k̄`, hence preserves a full flag of
`k̄^N`. The resulting representation of the points of `H` over `k̄` in `GL_N(k̄)` is injective
because `H ⟶ GL_N` is a closed immersion, so the group of these points is solvable.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open AlgebraicGeometry Langlands.AlgebraicGeometry.AffinePoints Langlands.Grassmannian
open scoped TensorProduct CategoryTheory.MonObj

namespace Langlands.GroupScheme.FlagScheme

/-- The points of the flag locus over a `k`-algebra `A`: stable points of the quotient
Grassmannian `G(rank N, A ⊗[k] (Idx N → k); A)`. -/
abbrev Pt (k : Type u) [CommRing k] (N : ℕ) (A : Type u) [CommRing A] [Algebra k A] : Type u :=
  {P : Module.Grassmannian A (A ⊗[k] (FlagLocus.Idx N → k)) (FlagLocus.rank N) //
    FlagLocus.Stable k P}

variable {k : Type u} [CommRing k] {N : ℕ}

/-- Base change of a point of the flag locus along a `k`-algebra map. -/
def Pt.map {A B : Type u} [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]
    (φ : A →ₐ[k] B) (s : Pt k N A) : Pt k N B :=
  ⟨Module.Grassmannian.map φ s.1, FlagLocus.Stable.map k s.2 φ⟩

/-- The action of `GL_N(A)` on the points of the flag locus over `A`. -/
def Pt.smul {A : Type u} [CommRing A] [Algebra k A] (g : GL (Fin N) A) (s : Pt k N A) :
    Pt k N A :=
  ⟨FlagLocus.smul k g s.1, FlagLocus.Stable.smul k s.2 g⟩

section Witness

variable (Z : Scheme.{u}) (q : Z ⟶ Spec (CommRingCat.of k))
  (ptZ : ∀ (A : Type u) [CommRing A] [Algebra k A],
    Pt k N A ≃ {g : Spec (CommRingCat.of A) ⟶ Z //
      g ≫ q = Spec.map (CommRingCat.ofHom (algebraMap k A))})

/-- The points of the flag locus over `A` are the affine points of `Z` over `Spec k`. -/
def ptOver (A : Type u) [CommRing A] [Algebra k A] :
    Pt k N A ≃ (specOver (R := k) A ⟶ Over.mk q) :=
  (ptZ A).trans
    { toFun := fun g => Over.homMk g.1 g.2
      invFun := fun x => ⟨x.left, Over.w x⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => Over.OverMorphism.ext rfl }

variable (hptZ : ∀ (A B : Type u) [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]
  (φ : A →ₐ[k] B) (s : Pt k N A),
  (ptZ B (s.map φ)).1 = Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ (ptZ A s).1)

include hptZ in
theorem ptOver_map {A B : Type u} [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]
    (φ : A →ₐ[k] B) (s : Pt k N A) :
    ptOver Z q ptZ B (s.map φ) = specMapOver φ ≫ ptOver Z q ptZ A s :=
  Over.OverMorphism.ext (hptZ A B φ s)

include hptZ in
/-- The natural action on points comes from a scheme action of `GL_N`. -/
theorem exists_action :
    ∃ a : SchemeAction (GeneralLinear.groupScheme (Fin N) (CommRingCat.of k)) (Over.mk q),
      ∀ (A : Type u) [CommRing A] [Algebra k A]
        (h : specOver (R := k) A ⟶ (GeneralLinear.groupScheme (Fin N) (CommRingCat.of k)).X)
        (y : specOver (R := k) A ⟶ Over.mk q),
        a.act h y = ptOver Z q ptZ A
          (((ptOver Z q ptZ A).symm y).smul (GeneralLinear.matrixOf h)) := by
  refine GeneralLinear.exists_schemeAction_of_affine
    (fun A _ _ g y => ptOver Z q ptZ A (((ptOver Z q ptZ A).symm y).smul g)) ?_ ?_ ?_
  · intro A B _ _ _ _ φ g y
    obtain ⟨s, rfl⟩ := (ptOver Z q ptZ A).surjective y
    change ptOver Z q ptZ B (((ptOver Z q ptZ B).symm (specMapOver φ ≫ ptOver Z q ptZ A s)).smul
        (Matrix.GeneralLinearGroup.map φ.toRingHom g)) =
      specMapOver φ ≫ ptOver Z q ptZ A (((ptOver Z q ptZ A).symm (ptOver Z q ptZ A s)).smul g)
    rw [← ptOver_map Z q ptZ hptZ, Equiv.symm_apply_apply, Equiv.symm_apply_apply,
      ← ptOver_map Z q ptZ hptZ]
    exact congrArg (ptOver Z q ptZ B)
      (Subtype.ext (FlagLocus.map_smul_point k φ g s.1).symm)
  · intro A _ _ y
    obtain ⟨s, rfl⟩ := (ptOver Z q ptZ A).surjective y
    change ptOver Z q ptZ A (((ptOver Z q ptZ A).symm (ptOver Z q ptZ A s)).smul 1) = _
    rw [Equiv.symm_apply_apply]
    exact congrArg (ptOver Z q ptZ A) (Subtype.ext (FlagLocus.one_smul k s.1))
  · intro A _ _ g g' y
    obtain ⟨s, rfl⟩ := (ptOver Z q ptZ A).surjective y
    change ptOver Z q ptZ A (((ptOver Z q ptZ A).symm (ptOver Z q ptZ A s)).smul (g * g')) =
      ptOver Z q ptZ A (((ptOver Z q ptZ A).symm (ptOver Z q ptZ A
        (((ptOver Z q ptZ A).symm (ptOver Z q ptZ A s)).smul g'))).smul g)
    simp only [Equiv.symm_apply_apply]
    exact congrArg (ptOver Z q ptZ A) (Subtype.ext (FlagLocus.mul_smul k g g' s.1))

end Witness

section Stabilizer

variable {k : Type u} [Field k] {N : ℕ} (Z : Scheme.{u}) (q : Z ⟶ Spec (CommRingCat.of k))
  (ptZ : ∀ (A : Type u) [CommRing A] [Algebra k A],
    Pt k N A ≃ {g : Spec (CommRingCat.of A) ⟶ Z //
      g ≫ q = Spec.map (CommRingCat.ofHom (algebraMap k A))})
  (a : SchemeAction (GeneralLinear.groupScheme (Fin N) (CommRingCat.of k)) (Over.mk q))
  (ha : ∀ (A : Type u) [CommRing A] [Algebra k A]
    (h : specOver (R := k) A ⟶ (GeneralLinear.groupScheme (Fin N) (CommRingCat.of k)).X)
    (y : specOver (R := k) A ⟶ Over.mk q),
    a.act h y = ptOver Z q ptZ A (((ptOver Z q ptZ A).symm y).smul (GeneralLinear.matrixOf h)))

include ha in
/-- If a subgroup `H` fixes a rational point, then the points of `H` over any test object `T`
that is identified, after precomposition, with an affine point over a field `K` form a solvable
group. -/
theorem isSolvable_points_of_isFixed (x : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ Over.mk q)
    {H : GroupScheme (Spec (CommRingCat.of k))}
    (i : H ⟶ GeneralLinear.groupScheme (Fin N) (CommRingCat.of k))
    (hx : (a.restrict i).IsFixed x) (K : Type u) [Field K] [Algebra k K]
    (T : Over (Spec (CommRingCat.of k))) (e : specOver (R := k) K ⟶ T)
    (he : ∀ g g' : T ⟶ H.X, e ≫ g ≫ i.hom.hom = e ≫ g' ≫ i.hom.hom → g = g') :
    Group.IsSolvable (T ⟶ H.X) := by
  let ρ : (T ⟶ H.X) →* GL (Fin N) K :=
    MonoidHom.mk' (fun g => GeneralLinear.matrixOf (e ≫ g ≫ i.hom.hom)) (fun g g' => by
      simp only [MonObj.mul_comp, MonObj.comp_mul, GeneralLinear.matrixOf_mul])
  have hρ : Function.Injective ρ := fun g g' hg =>
    he g g' (GeneralLinear.matrixOf_injective hg)
  let s := (ptOver Z q ptZ K).symm (toUnit (specOver (R := k) K) ≫ x)
  have hfix : ∀ g, FlagLocus.smul k (ρ g) s.1 = s.1 := by
    intro g
    have h1 := hx (specOver (R := k) K) (toUnit _) (e ≫ g)
    rw [SchemeAction.restrict_act, ha] at h1
    have h2 := (Equiv.eq_symm_apply _).mpr h1
    have h3 := congrArg Subtype.val h2
    rw [Category.assoc] at h3
    exact h3
  obtain ⟨F, hF, hdim, hpres⟩ := FlagLocus.exists_fullFlag s.1 s.2
  exact LinearAlgebra.isSolvable_of_injective_representation_fullFlag F hF hdim ρ hρ
    fun g => hpres (ρ g) (hfix g)

include ha in
/-- A closed subgroup fixing a rational point is solvable. -/
theorem isSolvableGroupScheme_of_isFixed (x : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ Over.mk q)
    (H : GroupScheme (Spec (CommRingCat.of k)))
    (i : H ⟶ GeneralLinear.groupScheme (Fin N) (CommRingCat.of k))
    (hi : IsClosedSubgroup i) (hx : (a.restrict i).IsFixed x) : IsSolvableGroupScheme H := by
  have : IsClosedImmersion i.hom.hom.left := hi
  let e : specOver (R := k) (AlgebraicClosure k) ⟶
      (Over.map (toAlgebraicClosure k)).obj (Over.mk (𝟙 _)) :=
    Over.homMk (𝟙 _) (by simp)
  have he : ∀ g g' : (Over.map (toAlgebraicClosure k)).obj (Over.mk (𝟙 _)) ⟶ H.X,
      e ≫ g ≫ i.hom.hom = e ≫ g' ≫ i.hom.hom → g = g' := by
    intro g g' hg
    have h := congrArg CommaMorphism.left hg
    simp only [Over.comp_left, e, Over.homMk_left, Category.id_comp] at h
    exact Over.OverMorphism.ext ((cancel_mono i.hom.hom.left).mp h)
  have := isSolvable_points_of_isFixed Z q ptZ a ha x i hx (AlgebraicClosure k) _ e he
  exact Group.isSolvable_of_isSolvable_injective
    (f := (baseChangePointsEquiv (toAlgebraicClosure k) H (Over.mk (𝟙 _))).toMonoidHom)
    (MulEquiv.injective _)

end Stabilizer

end FlagScheme

/-- Over an algebraically closed field, `GL_N` acts on the proper nonempty scheme of full flags,
and every closed subgroup fixing a rational point is solvable. -/
theorem generalLinearSolvableStabilizer : GeneralLinearSolvableStabilizerStatement.{u} := by
  intro k _ _ N
  obtain ⟨Gr, p, pt, hnat, m, ιP, hιP, hπ⟩ :=
    Module.Grassmannian.exists_scheme_represents_and_isClosedImmersion_toProjSpace k
      (Grassmannian.FlagLocus.Idx N → k) (Grassmannian.FlagLocus.rank N)
  obtain ⟨Z, ιZ, ptZ, hιZ, hptZ⟩ :=
    Scheme.exists_isClosedImmersion_represents_of_forall_exists_ideal k
      (fun A _ _ => Module.Grassmannian A (A ⊗[k] (Grassmannian.FlagLocus.Idx N → k))
        (Grassmannian.FlagLocus.rank N))
      (fun _ _ _ _ _ _ φ P => Module.Grassmannian.map φ P) Gr p pt hnat
      (fun _ _ _ P => Grassmannian.FlagLocus.Stable k P)
      (fun _ _ _ P => Grassmannian.FlagLocus.exists_ideal_stable_map_iff k P)
  have := hιZ
  have := hιP
  have hZ : ∀ (A B : Type u) [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]
      (φ : A →ₐ[k] B) (s : FlagScheme.Pt k N A),
      (ptZ B (s.map φ)).1 = Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ (ptZ A s).1 := by
    intro A B _ _ _ _ φ s
    rw [← cancel_mono ιZ, Category.assoc, hptZ, hptZ]
    exact hnat A B φ s.1
  obtain ⟨a, ha⟩ := FlagScheme.exists_action Z (ιZ ≫ p) ptZ hZ
  refine ⟨Over.mk (ιZ ≫ p), a, ?_, ?_, fun x H i hi hx =>
    FlagScheme.isSolvableGroupScheme_of_isFixed Z (ιZ ≫ p) ptZ a ha x H i hi hx⟩
  · change IsProper (ιZ ≫ p)
    rw [← hπ]
    infer_instance
  · obtain ⟨g, -⟩ := ptZ k
      ⟨Grassmannian.FlagLocus.stdPoint N k k, Grassmannian.FlagLocus.stable_stdPoint⟩
    exact ⟨g.base (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum k)⟩

end Langlands.GroupScheme
