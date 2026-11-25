/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FpqcSingletonFullyFaithful
import WeilConjectures.AlgebraicGeometry.DescentPullbackConstruction

/-!
# Canonical comparisons of pullback functors on scheme descent data

Source: Stacks Project, Descent, Tags 02VS(3) and 023Y(1)--(2)
(blueprint: lem-galois-fpqc-pullback-canonical-iso).
-/

@[expose] public section

universe v

namespace AlgebraicGeometry

open CategoryTheory CategoryTheory.Limits

private def projectPoint {X T Z : Scheme.{v}} {V : Over X} {W : Over T}
    {r : T ⟶ X} (q : W.left ⟶ V.left) (hq : q ≫ V.hom = W.hom ≫ r)
    {f : Z ⟶ T} (z : Over.mk f ⟶ W) : Over.mk (f ≫ r) ⟶ V :=
  Over.homMk (z.left ≫ q) (by
    rw [Category.assoc, hq, ← Category.assoc]
    exact congrArg (fun k ↦ k ≫ r) (Over.w z))

private lemma transport_naturality_left {S X Z Z' : Scheme.{v}} {a : X ⟶ S}
    {V : Over X} (D : Over.DescentDatum a V) (k : Z' ⟶ Z)
    (f g : Z ⟶ X) (h : f ≫ a = g ≫ a) (z : Over.mk f ⟶ V) :
    (D.transport (k ≫ f) (k ≫ g) (by simp only [Category.assoc, h])
      (Over.homMk (k ≫ z.left) (by simp))).left =
        k ≫ (D.transport f g h z).left := by
  exact congrArg (fun z ↦ z.left) (D.transport_homMk_comp k f g h z)

private lemma transport_congr_left {S X Z : Scheme.{v}} {a : X ⟶ S}
    {V : Over X} (D : Over.DescentDatum a V)
    (f₀ f₁ g₀ g₁ : Z ⟶ X) (h : f₀ ≫ a = f₁ ≫ a) (h' : g₀ ≫ a = g₁ ≫ a)
    (z : Over.mk f₀ ⟶ V) (w : Over.mk g₀ ⟶ V)
    (hf : f₀ = g₀) (hg : f₁ = g₁) (hz : z.left = w.left) :
    (D.transport f₀ f₁ h z).left = (D.transport g₀ g₁ h' w).left := by
  subst g₀
  subst g₁
  have : z = w := Over.OverMorphism.ext hz
  subst w
  rfl

private lemma projectPoint_transport {S X T Z : Scheme.{v}}
    {a : X ⟶ S} {b : T ⟶ S} {r : T ⟶ X} (hr : r ≫ a = b)
    {D : Over.DescentDataCategory a} {E : Over.DescentDataCategory b}
    {q : E.V.left ⟶ D.V.left} (hq : q ≫ D.V.hom = E.V.hom ≫ r)
    (bc : Over.DescentDatum.IsBaseChange hr hq D.datum E.datum)
    (f g : Z ⟶ T) (h : f ≫ b = g ≫ b) (z : Over.mk f ⟶ E.V) :
    projectPoint q hq (E.datum.transport f g h z) =
      D.datum.transport (f ≫ r) (g ≫ r)
        (by rw [Category.assoc, Category.assoc, hr, h]) (projectPoint q hq z) := by
  apply Over.OverMorphism.ext
  exact (bc f g h z).symm

section Comparison

variable {S X T : Scheme.{v}} {a : X ⟶ S} {b : T ⟶ S}
    {r₀ r₁ : T ⟶ X} (h₀ : r₀ ≫ a = b) (h₁ : r₁ ≫ a = b)
    (D : Over.DescentDataCategory a) (E F : Over.DescentDataCategory b)
    (q₀ : E.V.left ⟶ D.V.left) (q₁ : F.V.left ⟶ D.V.left)
    (hq₀ : q₀ ≫ D.V.hom = E.V.hom ≫ r₀)
    (hq₁ : q₁ ≫ D.V.hom = F.V.hom ≫ r₁)

private def comparisonPoint {Z : Scheme.{v}} (f : Z ⟶ T) (z : Over.mk f ⟶ E.V) :
    Over.mk (f ≫ r₁) ⟶ D.V :=
  D.datum.transport (f ≫ r₀) (f ≫ r₁)
    (by rw [Category.assoc, Category.assoc, h₀, h₁]) (projectPoint q₀ hq₀ z)

private noncomputable def comparisonArrow
    (hp₁ : IsPullback q₁ F.V.hom D.V.hom r₁) : E.V ⟶ F.V :=
  Over.homMk (hp₁.lift
    (comparisonPoint h₀ h₁ D E q₀ hq₀ E.V.hom (𝟙 E.V)).left E.V.hom (Over.w _))
    (by simp)

private lemma comparisonArrow_point
    (hp₁ : IsPullback q₁ F.V.hom D.V.hom r₁)
    {Z : Scheme.{v}} (f : Z ⟶ T) (z : Over.mk f ⟶ E.V) :
    projectPoint q₁ hq₁ (z ≫ comparisonArrow h₀ h₁ D E F q₀ q₁ hq₀ hp₁) =
      comparisonPoint h₀ h₁ D E q₀ hq₀ f z := by
  apply Over.OverMorphism.ext
  change (z.left ≫ hp₁.lift _ _ _) ≫ q₁ = _
  simp only [Category.assoc, IsPullback.lift_fst]
  have hn := transport_naturality_left D.datum z.left
    (E.V.hom ≫ r₀) (E.V.hom ≫ r₁)
    (by rw [Category.assoc, Category.assoc, h₀, h₁])
    (Over.homMk q₀ hq₀)
  have hn' : (D.datum.transport
      (z.left ≫ (E.V.hom ≫ r₀)) (z.left ≫ (E.V.hom ≫ r₁))
      (by simp only [Category.assoc, h₀, h₁])
      (Over.homMk (z.left ≫ q₀) (by simp [hq₀]))).left =
        (comparisonPoint h₀ h₁ D E q₀ hq₀ f z).left := by
    apply transport_congr_left
    · simpa only [← Category.assoc, Over.mk_hom] using
        congrArg (fun k ↦ k ≫ r₀) (Over.w z)
    · simpa only [← Category.assoc, Over.mk_hom] using
        congrArg (fun k ↦ k ≫ r₁) (Over.w z)
    · rfl
  have hn'' : z.left ≫
      (comparisonPoint h₀ h₁ D E q₀ hq₀ E.V.hom (𝟙 E.V)).left =
      (D.datum.transport (z.left ≫ (E.V.hom ≫ r₀))
        (z.left ≫ (E.V.hom ≫ r₁)) _ (Over.homMk (z.left ≫ q₀) _)).left :=
    hn.symm
  exact hn''.trans hn'

private noncomputable def comparisonHom
    (hp₁ : IsPullback q₁ F.V.hom D.V.hom r₁)
    (bc₀ : Over.DescentDatum.IsBaseChange h₀ hq₀ D.datum E.datum)
    (bc₁ : Over.DescentDatum.IsBaseChange h₁ hq₁ D.datum F.datum) : E ⟶ F where
  hom := comparisonArrow h₀ h₁ D E F q₀ q₁ hq₀ hp₁
  commutes := by
    intro Z f g h z
    apply Over.OverMorphism.ext
    apply hp₁.hom_ext
    · have hh : projectPoint q₁ hq₁
          (F.datum.transport f g h
            (z ≫ comparisonArrow h₀ h₁ D E F q₀ q₁ hq₀ hp₁)) =
          projectPoint q₁ hq₁
            (E.datum.transport f g h z ≫
              comparisonArrow h₀ h₁ D E F q₀ q₁ hq₀ hp₁) := by
        rw [projectPoint_transport h₁ hq₁ bc₁, comparisonArrow_point,
          comparisonArrow_point]
        unfold comparisonPoint
        rw [projectPoint_transport h₀ hq₀ bc₀,
          D.datum.transport_transport, D.datum.transport_transport]
      exact congrArg (fun k ↦ k.left) hh
    · exact (Over.w _).trans (Over.w _).symm

private lemma comparisonHom_inverse
    (hp₀ : IsPullback q₀ E.V.hom D.V.hom r₀)
    (hp₁ : IsPullback q₁ F.V.hom D.V.hom r₁)
    (bc₀ : Over.DescentDatum.IsBaseChange h₀ hq₀ D.datum E.datum)
    (bc₁ : Over.DescentDatum.IsBaseChange h₁ hq₁ D.datum F.datum) :
    comparisonHom h₀ h₁ D E F q₀ q₁ hq₀ hq₁ hp₁ bc₀ bc₁ ≫
      comparisonHom h₁ h₀ D F E q₁ q₀ hq₁ hq₀ hp₀ bc₁ bc₀ = 𝟙 E := by
  apply Over.DescentDataCategory.Hom.ext
  apply Over.OverMorphism.ext
  apply hp₀.hom_ext
  · have hh := comparisonArrow_point h₁ h₀ D F E q₁ q₀ hq₁ hq₀ hp₀ E.V.hom
      (comparisonArrow h₀ h₁ D E F q₀ q₁ hq₀ hp₁)
    unfold comparisonPoint at hh
    have he := comparisonArrow_point h₀ h₁ D E F q₀ q₁ hq₀ hq₁ hp₁ E.V.hom (𝟙 E.V)
    have he' : projectPoint q₁ hq₁
        (comparisonArrow h₀ h₁ D E F q₀ q₁ hq₀ hp₁) =
        comparisonPoint h₀ h₁ D E q₀ hq₀ E.V.hom (𝟙 E.V) := by
      apply Over.OverMorphism.ext
      simpa [projectPoint] using congrArg (fun k ↦ k.left) he
    conv_rhs at hh => rw [he']
    unfold comparisonPoint at hh
    rw [D.datum.transport_transport, D.datum.transport_self] at hh
    exact congrArg (fun k ↦ k.left) hh
  · exact (Over.w _).trans (by simp)

private noncomputable def comparisonIso
    (hp₀ : IsPullback q₀ E.V.hom D.V.hom r₀)
    (hp₁ : IsPullback q₁ F.V.hom D.V.hom r₁)
    (bc₀ : Over.DescentDatum.IsBaseChange h₀ hq₀ D.datum E.datum)
    (bc₁ : Over.DescentDatum.IsBaseChange h₁ hq₁ D.datum F.datum) : E ≅ F where
  hom := comparisonHom h₀ h₁ D E F q₀ q₁ hq₀ hq₁ hp₁ bc₀ bc₁
  inv := comparisonHom h₁ h₀ D F E q₁ q₀ hq₁ hq₀ hp₀ bc₁ bc₀
  hom_inv_id := comparisonHom_inverse h₀ h₁ D E F q₀ q₁ hq₀ hq₁ hp₀ hp₁ bc₀ bc₁
  inv_hom_id := comparisonHom_inverse h₁ h₀ D F E q₁ q₀ hq₁ hq₀ hp₁ hp₀ bc₁ bc₀

end Comparison

private lemma comparisonPoint_natural {S X T Z : Scheme.{v}}
    {a : X ⟶ S} {b : T ⟶ S} {r₀ r₁ : T ⟶ X}
    (h₀ : r₀ ≫ a = b) (h₁ : r₁ ≫ a = b)
    {D D' : Over.DescentDataCategory a} (m : D ⟶ D')
    {E E' : Over.DescentDataCategory b}
    (q : E.V.left ⟶ D.V.left) (q' : E'.V.left ⟶ D'.V.left)
    (hq : q ≫ D.V.hom = E.V.hom ≫ r₀)
    (hq' : q' ≫ D'.V.hom = E'.V.hom ≫ r₀)
    (n : E ⟶ E') (hn : n.hom.left ≫ q' = q ≫ m.hom.left)
    (f : Z ⟶ T) (z : Over.mk f ⟶ E.V) :
    comparisonPoint h₀ h₁ D' E' q' hq' f (z ≫ n.hom) =
      comparisonPoint h₀ h₁ D E q hq f z ≫ m.hom := by
  unfold comparisonPoint
  have hz : projectPoint q' hq' (z ≫ n.hom) = projectPoint q hq z ≫ m.hom := by
    apply Over.OverMorphism.ext
    change (z.left ≫ n.hom.left) ≫ q' = (z.left ≫ q) ≫ m.hom.left
    simp only [Category.assoc, hn]
  rw [hz, m.commutes]

private lemma comparisonIso_natural {S X T : Scheme.{v}}
    {a : X ⟶ S} {b : T ⟶ S} {r₀ r₁ : T ⟶ X}
    (h₀ : r₀ ≫ a = b) (h₁ : r₁ ≫ a = b)
    (F₀ F₁ : Over.DescentDataCategory a ⥤ Over.DescentDataCategory b)
    (q₀ : ∀ D, (F₀.obj D).V.left ⟶ D.V.left)
    (q₁ : ∀ D, (F₁.obj D).V.left ⟶ D.V.left)
    (hq₀ : ∀ D, q₀ D ≫ D.V.hom = (F₀.obj D).V.hom ≫ r₀)
    (hq₁ : ∀ D, q₁ D ≫ D.V.hom = (F₁.obj D).V.hom ≫ r₁)
    (hp₀ : ∀ D, IsPullback (q₀ D) (F₀.obj D).V.hom D.V.hom r₀)
    (hp₁ : ∀ D, IsPullback (q₁ D) (F₁.obj D).V.hom D.V.hom r₁)
    (bc₀ : ∀ D, Over.DescentDatum.IsBaseChange h₀ (hq₀ D) D.datum (F₀.obj D).datum)
    (bc₁ : ∀ D, Over.DescentDatum.IsBaseChange h₁ (hq₁ D) D.datum (F₁.obj D).datum)
    (hn₀ : ∀ D E (m : D ⟶ E), (F₀.map m).hom.left ≫ q₀ E = q₀ D ≫ m.hom.left)
    (hn₁ : ∀ D E (m : D ⟶ E), (F₁.map m).hom.left ≫ q₁ E = q₁ D ≫ m.hom.left)
    {D E : Over.DescentDataCategory a} (m : D ⟶ E) :
    F₀.map m ≫ (comparisonIso h₀ h₁ E (F₀.obj E) (F₁.obj E)
      (q₀ E) (q₁ E) (hq₀ E) (hq₁ E) (hp₀ E) (hp₁ E) (bc₀ E) (bc₁ E)).hom =
    (comparisonIso h₀ h₁ D (F₀.obj D) (F₁.obj D)
      (q₀ D) (q₁ D) (hq₀ D) (hq₁ D) (hp₀ D) (hp₁ D) (bc₀ D) (bc₁ D)).hom ≫
      F₁.map m := by
  apply Over.DescentDataCategory.Hom.ext
  apply Over.OverMorphism.ext
  apply (hp₁ E).hom_ext
  · have hh := comparisonArrow_point h₀ h₁ E (F₀.obj E) (F₁.obj E)
      (q₀ E) (q₁ E) (hq₀ E) (hq₁ E) (hp₁ E) (F₀.obj D).V.hom (F₀.map m).hom
    have hn := comparisonPoint_natural h₀ h₁ m (q₀ D) (q₀ E)
      (hq₀ D) (hq₀ E) (F₀.map m) (hn₀ D E m) (F₀.obj D).V.hom (𝟙 _)
    have hn' : (comparisonPoint h₀ h₁ E (F₀.obj E) (q₀ E) (hq₀ E)
        (F₀.obj D).V.hom (F₀.map m).hom).left =
        (comparisonPoint h₀ h₁ D (F₀.obj D) (q₀ D) (hq₀ D)
          (F₀.obj D).V.hom (𝟙 _)).left ≫ m.hom.left := by
      simpa [comparisonPoint, projectPoint] using congrArg (fun k ↦ k.left) hn
    have hh' := (congrArg (fun k ↦ k.left) hh).trans hn'
    change ((F₀.map m).hom.left ≫ _) ≫ q₁ E = (_ ≫ (F₁.map m).hom.left) ≫ q₁ E
    simp only [Category.assoc, hn₁ D E m]
    simpa [projectPoint, comparisonPoint, comparisonArrow, comparisonIso, comparisonHom,
      Category.assoc] using hh'
  · exact (Over.w _).trans (Over.w _).symm

private noncomputable def comparisonNatIso {S X T : Scheme.{v}}
    {a : X ⟶ S} {b : T ⟶ S} {r₀ r₁ : T ⟶ X}
    (h₀ : r₀ ≫ a = b) (h₁ : r₁ ≫ a = b)
    (F₀ F₁ : Over.DescentDataCategory a ⥤ Over.DescentDataCategory b)
    (q₀ : ∀ D, (F₀.obj D).V.left ⟶ D.V.left)
    (q₁ : ∀ D, (F₁.obj D).V.left ⟶ D.V.left)
    (hq₀ : ∀ D, q₀ D ≫ D.V.hom = (F₀.obj D).V.hom ≫ r₀)
    (hq₁ : ∀ D, q₁ D ≫ D.V.hom = (F₁.obj D).V.hom ≫ r₁)
    (hp₀ : ∀ D, IsPullback (q₀ D) (F₀.obj D).V.hom D.V.hom r₀)
    (hp₁ : ∀ D, IsPullback (q₁ D) (F₁.obj D).V.hom D.V.hom r₁)
    (bc₀ : ∀ D, Over.DescentDatum.IsBaseChange h₀ (hq₀ D) D.datum (F₀.obj D).datum)
    (bc₁ : ∀ D, Over.DescentDatum.IsBaseChange h₁ (hq₁ D) D.datum (F₁.obj D).datum)
    (hn₀ : ∀ D E (m : D ⟶ E), (F₀.map m).hom.left ≫ q₀ E = q₀ D ≫ m.hom.left)
    (hn₁ : ∀ D E (m : D ⟶ E), (F₁.map m).hom.left ≫ q₁ E = q₁ D ≫ m.hom.left) :
    F₀ ≅ F₁ :=
  NatIso.ofComponents (fun D ↦ comparisonIso h₀ h₁ D (F₀.obj D) (F₁.obj D)
    (q₀ D) (q₁ D) (hq₀ D) (hq₁ D) (hp₀ D) (hp₁ D) (bc₀ D) (bc₁ D))
    (fun m ↦ comparisonIso_natural h₀ h₁ F₀ F₁ q₀ q₁ hq₀ hq₁ hp₀ hp₁ bc₀ bc₁ hn₀ hn₁ m)

private lemma baseChange_comp {S X T U : Scheme.{v}}
    {a : X ⟶ S} {b : T ⟶ S} {c : U ⟶ S}
    {r : T ⟶ X} {t : U ⟶ T} (hr : r ≫ a = b) (ht : t ≫ b = c)
    (hrt : (t ≫ r) ≫ a = c)
    {D : Over.DescentDataCategory a} {E : Over.DescentDataCategory b}
    {F : Over.DescentDataCategory c} {q : E.V.left ⟶ D.V.left}
    {p : F.V.left ⟶ E.V.left}
    (hq : q ≫ D.V.hom = E.V.hom ≫ r)
    (hp : p ≫ E.V.hom = F.V.hom ≫ t)
    (hpq : (p ≫ q) ≫ D.V.hom = F.V.hom ≫ (t ≫ r))
    (bcq : Over.DescentDatum.IsBaseChange hr hq D.datum E.datum)
    (bcp : Over.DescentDatum.IsBaseChange ht hp E.datum F.datum) :
    Over.DescentDatum.IsBaseChange hrt hpq D.datum F.datum := by
  intro Z f g h z
  have hp' := projectPoint_transport ht hp bcp f g h z
  have hq' := projectPoint_transport hr hq bcq (f ≫ t) (g ≫ t)
    (by rw [Category.assoc, Category.assoc, ht, h]) (projectPoint p hp z)
  have hh : projectPoint q hq (projectPoint p hp (F.datum.transport f g h z)) =
      D.datum.transport ((f ≫ t) ≫ r) ((g ≫ t) ≫ r)
        (by simp only [Category.assoc, hr, ht, h])
        (projectPoint q hq (projectPoint p hp z)) := by
    rw [hp', hq']
  have he : (D.datum.transport ((f ≫ t) ≫ r) ((g ≫ t) ≫ r)
      (by simp only [Category.assoc, hr, ht, h])
      (projectPoint q hq (projectPoint p hp z))).left =
      (D.datum.transport (f ≫ (t ≫ r)) (g ≫ (t ≫ r))
        (by simp only [Category.assoc, hr, ht, h])
        (projectPoint (p ≫ q) hpq z)).left := by
    apply transport_congr_left <;> simp [projectPoint, Category.assoc]
  exact he.symm.trans (by simpa [projectPoint, Category.assoc] using
    (congrArg (fun k ↦ k.left) hh).symm)

private theorem pullback_exists {S X T : Scheme.{v}} (a : X ⟶ S) (b : T ⟶ S)
    (r : T ⟶ X) (hr : r ≫ a = b) :
    ∃ (F : Over.DescentDataCategory a ⥤ Over.DescentDataCategory b)
      (q : ∀ D, (F.obj D).V.left ⟶ D.V.left)
      (hq : ∀ D, q D ≫ D.V.hom = (F.obj D).V.hom ≫ r),
      (∀ D, IsPullback (q D) (F.obj D).V.hom D.V.hom r ∧
        Over.DescentDatum.IsBaseChange hr (hq D) D.datum (F.obj D).datum) ∧
      ∀ D E (m : D ⟶ E), (F.map m).hom.left ≫ q E = q D ≫ m.hom.left := by
  subst b
  obtain ⟨F, q, hp, hn⟩ := descent_pullback_construction a r
  exact ⟨F, q, fun D ↦ (hp D).choose, fun D ↦ (hp D).choose_spec, hn⟩

-- Keep the existing signature, including its named proof argument to `pull`.
set_option linter.unusedVariables false in
/-- Canonical comparisons of pullback of descent data over a fixed scheme.
Source: Stacks Project, Descent, Tags 023Y(1)--(2) and 02VS(3)
(blueprint: lem-galois-fpqc-pullback-canonical-iso).

The functors are specified by their fibre-product projections `q`, the universal property
`IsPullback`, the pulled-back datum `IsBaseChange`, and the equation for their maps.
The two-map comparison is specified by transporting the universal point of the first
pullback along the pair of maps to `X`. The composition comparison preserves the projection
back to the original scheme; together with being over `U`, this specifies the canonical
associativity isomorphism uniquely.

Proof: (1) The pair `(r₀,r₁)` defines a map to `X ×_S X` by the universal property
[def-pc-fibre-product]. Pull back the descent isomorphism
[proposition-jacobian-over-ground-field--1] along this pair to obtain the comparison; compatibility
of morphisms of descent data gives naturality. (2) On `T ×_S T`, the required descent-morphism
equation follows by applying the cocycle identity twice on `X ×_S X ×_S X`; inverse transport gives
the inverse morphism. (3) For composable maps, the universal property [def-pc-fibre-product]
identifies the iterated and direct pullbacks preserving both projections. Functoriality identifies
their descent data and morphisms, giving the natural associativity comparison. -/
theorem descent_pullback_canonical_iso (S : Scheme.{v}) :
    ∃ (pull : ∀ ⦃X T : Scheme.{v}⦄ (a : X ⟶ S) (b : T ⟶ S)
        (r : T ⟶ X) (hr : r ≫ a = b), Over.DescentDataCategory a ⥤ Over.DescentDataCategory b)
      (q : ∀ ⦃X T : Scheme.{v}⦄ (a : X ⟶ S) (b : T ⟶ S)
        (r : T ⟶ X) (hr : r ≫ a = b) (D : Over.DescentDataCategory a),
          ((pull a b r hr).obj D).V.left ⟶ D.V.left)
      (hq : ∀ ⦃X T : Scheme.{v}⦄ (a : X ⟶ S) (b : T ⟶ S)
        (r : T ⟶ X) (hr : r ≫ a = b) (D : Over.DescentDataCategory a),
          q a b r hr D ≫ D.V.hom = ((pull a b r hr).obj D).V.hom ≫ r),
      (∀ ⦃X T : Scheme.{v}⦄ (a : X ⟶ S) (b : T ⟶ S)
          (r : T ⟶ X) (hr : r ≫ a = b) (D : Over.DescentDataCategory a),
        IsPullback (q a b r hr D) ((pull a b r hr).obj D).V.hom D.V.hom r ∧
          Over.DescentDatum.IsBaseChange (hr) (hq a b r hr D) D.datum
            ((pull a b r hr).obj D).datum) ∧
      (∀ ⦃X T : Scheme.{v}⦄ (a : X ⟶ S) (b : T ⟶ S)
          (r : T ⟶ X) (hr : r ≫ a = b)
          (D E : Over.DescentDataCategory a) (m : D ⟶ E),
        ((pull a b r hr).map m).hom.left ≫ q a b r hr E =
          q a b r hr D ≫ m.hom.left) ∧
      (∀ ⦃X T : Scheme.{v}⦄ (a : X ⟶ S) (b : T ⟶ S)
          (r₀ r₁ : T ⟶ X) (h₀ : r₀ ≫ a = b) (h₁ : r₁ ≫ a = b),
        ∃ e : pull a b r₀ h₀ ≅ pull a b r₁ h₁,
          ∀ D : Over.DescentDataCategory a,
            (e.hom.app D).hom.left ≫ q a b r₁ h₁ D =
              (D.datum.transport
                (((pull a b r₀ h₀).obj D).V.hom ≫ r₀)
                (((pull a b r₀ h₀).obj D).V.hom ≫ r₁)
                (by rw [Category.assoc, Category.assoc, h₀, h₁])
                (Over.homMk (q a b r₀ h₀ D) (hq a b r₀ h₀ D))).left) ∧
      (∀ ⦃X T U : Scheme.{v}⦄ (a : X ⟶ S) (b : T ⟶ S) (c : U ⟶ S)
          (r : T ⟶ X) (t : U ⟶ T) (hr : r ≫ a = b) (ht : t ≫ b = c)
          (hrt : (t ≫ r) ≫ a = c),
        ∃ e : pull a c (t ≫ r) hrt ≅ pull a b r hr ⋙ pull b c t ht,
          ∀ D : Over.DescentDataCategory a,
            (e.hom.app D).hom.left ≫ q b c t ht ((pull a b r hr).obj D) ≫
              q a b r hr D = q a c (t ≫ r) hrt D) := by
  classical
  let pull : ∀ ⦃X T : Scheme.{v}⦄ (a : X ⟶ S) (b : T ⟶ S)
      (r : T ⟶ X) (hr : r ≫ a = b),
      Over.DescentDataCategory a ⥤ Over.DescentDataCategory b :=
    fun {X T} a b r hr ↦ (pullback_exists a b r hr).choose
  let q : ∀ ⦃X T : Scheme.{v}⦄ (a : X ⟶ S) (b : T ⟶ S)
      (r : T ⟶ X) (hr : r ≫ a = b) (D : Over.DescentDataCategory a),
      ((pull a b r hr).obj D).V.left ⟶ D.V.left :=
    fun {X T} a b r hr ↦ (pullback_exists a b r hr).choose_spec.choose
  have hq : ∀ ⦃X T : Scheme.{v}⦄ (a : X ⟶ S) (b : T ⟶ S)
      (r : T ⟶ X) (hr : r ≫ a = b) (D : Over.DescentDataCategory a),
      q a b r hr D ≫ D.V.hom = ((pull a b r hr).obj D).V.hom ≫ r :=
    fun {X T} a b r hr ↦ (pullback_exists a b r hr).choose_spec.choose_spec.choose
  have hp : ∀ ⦃X T : Scheme.{v}⦄ (a : X ⟶ S) (b : T ⟶ S)
      (r : T ⟶ X) (hr : r ≫ a = b) (D : Over.DescentDataCategory a),
      IsPullback (q a b r hr D) ((pull a b r hr).obj D).V.hom D.V.hom r ∧
        Over.DescentDatum.IsBaseChange hr (hq a b r hr D) D.datum
          ((pull a b r hr).obj D).datum :=
    fun {X T} a b r hr ↦ (pullback_exists a b r hr).choose_spec.choose_spec.choose_spec.1
  have hn : ∀ ⦃X T : Scheme.{v}⦄ (a : X ⟶ S) (b : T ⟶ S)
      (r : T ⟶ X) (hr : r ≫ a = b) (D E : Over.DescentDataCategory a) (m : D ⟶ E),
      ((pull a b r hr).map m).hom.left ≫ q a b r hr E = q a b r hr D ≫ m.hom.left :=
    fun {X T} a b r hr ↦ (pullback_exists a b r hr).choose_spec.choose_spec.choose_spec.2
  refine ⟨pull, q, hq, hp, hn, ?_, ?_⟩
  · intro X T a b r₀ r₁ h₀ h₁
    refine ⟨comparisonNatIso h₀ h₁ (pull a b r₀ h₀) (pull a b r₁ h₁)
      (q a b r₀ h₀) (q a b r₁ h₁) (hq a b r₀ h₀) (hq a b r₁ h₁)
      (fun D ↦ (hp a b r₀ h₀ D).1) (fun D ↦ (hp a b r₁ h₁ D).1)
      (fun D ↦ (hp a b r₀ h₀ D).2) (fun D ↦ (hp a b r₁ h₁ D).2)
      (hn a b r₀ h₀) (hn a b r₁ h₁), ?_⟩
    intro D
    simp [comparisonNatIso, comparisonIso, comparisonHom, comparisonArrow,
      comparisonPoint, projectPoint]
  · intro X T U a b c r t hr ht hrt
    let F := pull a b r hr
    let G := pull b c t ht
    let H := pull a c (t ≫ r) hrt
    let qF := q a b r hr
    let qG := q b c t ht
    let qH := q a c (t ≫ r) hrt
    let qFG (D : Over.DescentDataCategory a) := qG (F.obj D) ≫ qF D
    have hqFG (D : Over.DescentDataCategory a) :
        qFG D ≫ D.V.hom = ((F ⋙ G).obj D).V.hom ≫ (t ≫ r) := by
      dsimp [qFG, qF, qG, F, G]
      simp only [Category.assoc, hq a b r hr D]
      rw [← Category.assoc, hq b c t ht _, Category.assoc]
    have hpFG (D : Over.DescentDataCategory a) :
        IsPullback (qFG D) ((F ⋙ G).obj D).V.hom D.V.hom (t ≫ r) :=
      (hp b c t ht (F.obj D)).1.paste_horiz (hp a b r hr D).1
    have bcFG (D : Over.DescentDataCategory a) :
        Over.DescentDatum.IsBaseChange hrt (hqFG D) D.datum ((F ⋙ G).obj D).datum :=
      baseChange_comp hr ht hrt (hq a b r hr D) (hq b c t ht (F.obj D))
        (hqFG D) (hp a b r hr D).2 (hp b c t ht (F.obj D)).2
    have hnFG (D E : Over.DescentDataCategory a) (m : D ⟶ E) :
        ((F ⋙ G).map m).hom.left ≫ qFG E = qFG D ≫ m.hom.left := by
      dsimp [qFG, qF, qG, F, G]
      rw [← Category.assoc, hn b c t ht _ _ _, Category.assoc, hn a b r hr D E m]
      simp only [Category.assoc]
    refine ⟨comparisonNatIso hrt hrt H (F ⋙ G) qH qFG (hq a c (t ≫ r) hrt)
      hqFG (fun D ↦ (hp a c (t ≫ r) hrt D).1) hpFG
      (fun D ↦ (hp a c (t ≫ r) hrt D).2) bcFG (hn a c (t ≫ r) hrt) hnFG, ?_⟩
    intro D
    change (comparisonArrow hrt hrt D (H.obj D) ((F ⋙ G).obj D)
      (qH D) (qFG D) (hq a c (t ≫ r) hrt D) (hpFG D)).left ≫
        qG (F.obj D) ≫ qF D = qH D
    change _ ≫ qFG D = qH D
    simp [comparisonArrow, comparisonPoint, projectPoint, Over.DescentDatum.transport_self]


end AlgebraicGeometry
