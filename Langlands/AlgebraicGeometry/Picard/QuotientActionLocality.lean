import Langlands.GroupScheme.CocycleTorsor
import Langlands.AbelianScheme.KernelBaseChange
import Langlands.AlgebraicGeometry.AlgebraicSpace.Basic
import Langlands.AlgebraicGeometry.SmoothSurjectiveEtaleLocalSections
import Langlands.AlgebraicGeometry.Descent.LocallyQuasiFiniteDescent.Proof
import Langlands.AlgebraicGeometry.AlgebraicSpace.FppfQuotientRepresentability
import Langlands.AlgebraicGeometry.Sites.OverFppfSheaf

/-! # Etale-local orbits for fppf quotients by smooth group actions -/

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard.QuotientActionLocality

open Langlands.GroupScheme Langlands.AlgebraicGeometry.AlgebraicSpace

/-- A presheaf `P` with an action of the points of a group scheme `H`, a homomorphism
`q : H ⟶ Q` whose kernel is exactly the stabilizer of every section, and an invariant map
`π : P ⟶ E` whose fibres are fppf-locally single orbits. -/
structure QuotientAction (S : Scheme.{u}) where
  /-- The acted-upon presheaf. -/
  P : (Over S)ᵒᵖ ⥤ Type (u + 1)
  /-- The target presheaf. -/
  E : (Over S)ᵒᵖ ⥤ Type (u + 1)
  /-- The invariant map. -/
  π : P ⟶ E
  /-- The acting group scheme. -/
  H : GroupScheme S
  /-- The quotient group scheme. -/
  Q : GroupScheme S
  /-- The quotient homomorphism. -/
  q : H ⟶ Q
  /-- The action of points of `H` on sections of `P`. -/
  act : ∀ {T : Over S}, (T ⟶ H.X) → P.obj (op T) → P.obj (op T)
  act_one : ∀ {T : Over S} (x : P.obj (op T)), act 1 x = x
  act_mul : ∀ {T : Over S} (h h' : T ⟶ H.X) (x : P.obj (op T)),
    act (h * h') x = act h (act h' x)
  map_act : ∀ {T T' : Over S} (a : T' ⟶ T) (h : T ⟶ H.X) (x : P.obj (op T)),
    P.map a.op (act h x) = act (a ≫ h) (P.map a.op x)
  π_act : ∀ {T : Over S} (h : T ⟶ H.X) (x : P.obj (op T)),
    π.app (op T) (act h x) = π.app (op T) x
  act_eq_self_iff : ∀ {T : Over S} (h : T ⟶ H.X) (x : P.obj (op T)),
    act h x = x ↔ h ≫ q.hom.hom = 1
  locally_orbit : ∀ {T : Over S} (x y : P.obj (op T)), π.app (op T) x = π.app (op T) y →
    ∃ R ∈ fppfTopology S T, ∀ ⦃V : Over S⦄ (g : V ⟶ T), R g →
      ∃ h : V ⟶ H.X, P.map g.op x = act h (P.map g.op y)

namespace QuotientAction

variable {S : Scheme.{u}} (D : QuotientAction S)

lemma act_inv_act {T : Over S} (h : T ⟶ D.H.X) (x : D.P.obj (op T)) :
    D.act h⁻¹ (D.act h x) = x := by
  rw [← D.act_mul, inv_mul_cancel, D.act_one]

lemma act_act_inv {T : Over S} (h : T ⟶ D.H.X) (x : D.P.obj (op T)) :
    D.act h (D.act h⁻¹ x) = x := by
  rw [← D.act_mul, mul_inv_cancel, D.act_one]

lemma comp_q_eq_of_act_eq {T : Over S} {h h' : T ⟶ D.H.X} {x : D.P.obj (op T)}
    (e : D.act h x = D.act h' x) : h ≫ D.q.hom.hom = h' ≫ D.q.hom.hom := by
  have h1 : D.act (h'⁻¹ * h) x = x := by
    rw [D.act_mul, e, act_inv_act]
  have h2 := (D.act_eq_self_iff _ x).mp h1
  rw [MonObj.mul_comp, GrpObj.inv_comp] at h2
  exact (inv_mul_eq_one.mp h2).symm

lemma act_eq_act_of_comp_q_eq {T : Over S} {h h' : T ⟶ D.H.X} (x : D.P.obj (op T))
    (e : h ≫ D.q.hom.hom = h' ≫ D.q.hom.hom) : D.act h x = D.act h' x := by
  have h1 : (h'⁻¹ * h) ≫ D.q.hom.hom = 1 := by
    rw [MonObj.mul_comp, GrpObj.inv_comp, e, inv_mul_cancel]
  have h2 := (D.act_eq_self_iff _ x).mpr h1
  rw [D.act_mul] at h2
  calc D.act h x = D.act h' (D.act h'⁻¹ (D.act h x)) := (act_act_inv D h' _).symm
    _ = D.act h' x := by rw [h2]

/-- `d` is the `Q`-valued difference of `x` and `y`: on every test where `x` is a translate
of `y` by a point `h` of `H`, the restriction of `d` is the image of `h`. -/
def IsDelta {T : Over S} (x y : D.P.obj (op T)) (d : T ⟶ D.Q.X) : Prop :=
  ∀ ⦃V : Over S⦄ (g : V ⟶ T) (h : V ⟶ D.H.X),
    D.P.map g.op x = D.act h (D.P.map g.op y) → g ≫ d = h ≫ D.q.hom.hom

lemma yoneda_isSheaf : Presieve.IsSheaf (fppfTopology S) (yoneda.obj D.Q.X) :=
  GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _

/-- Two maps to `Q` agreeing on an fppf covering sieve are equal. -/
lemma ext_of_mem {T : Over S} {R : Sieve T} (hR : R ∈ fppfTopology S T)
    {d d' : T ⟶ D.Q.X} (h : ∀ ⦃V : Over S⦄ (g : V ⟶ T), R g → g ≫ d = g ≫ d') : d = d' :=
  (D.yoneda_isSheaf.isSeparated R hR).ext (fun _ g hg ↦ h g hg)

lemma exists_isDelta {T : Over S} {x y : D.P.obj (op T)}
    (hxy : D.π.app (op T) x = D.π.app (op T) y) : ∃ d, D.IsDelta x y d := by
  obtain ⟨R, hR, hRx⟩ := D.locally_orbit x y hxy
  choose h hh using hRx
  let fam : Presieve.FamilyOfElements (yoneda.obj D.Q.X) R.arrows :=
    fun V g hg ↦ h g hg ≫ D.q.hom.hom
  have hc : fam.Compatible := by
    intro Y₁ Y₂ Z f₁ f₂ g₁ g₂ hg₁ hg₂ w
    change f₁ ≫ h g₁ hg₁ ≫ D.q.hom.hom = f₂ ≫ h g₂ hg₂ ≫ D.q.hom.hom
    rw [← Category.assoc, ← Category.assoc]
    apply D.comp_q_eq_of_act_eq (x := D.P.map (f₁ ≫ g₁).op y)
    have e₁ := congrArg (D.P.map f₁.op) (hh g₁ hg₁)
    have e₂ := congrArg (D.P.map f₂.op) (hh g₂ hg₂)
    rw [D.map_act, ← Functor.map_comp_apply, ← Functor.map_comp_apply,
      ← op_comp] at e₁ e₂
    rw [← e₁, w, e₂]
  obtain ⟨d, hd⟩ := (D.yoneda_isSheaf R hR fam hc).exists
  refine ⟨d, fun V g k hk ↦ ?_⟩
  apply D.ext_of_mem ((fppfTopology S).pullback_stable g hR)
  intro W a ha
  have e := hd (a ≫ g) ha
  change (a ≫ g) ≫ d = h (a ≫ g) ha ≫ D.q.hom.hom at e
  rw [← Category.assoc, e, ← Category.assoc]
  apply D.comp_q_eq_of_act_eq (x := D.P.map (a ≫ g).op y)
  rw [← hh (a ≫ g) ha]
  have := congrArg (D.P.map a.op) hk
  rw [D.map_act, ← Functor.map_comp_apply, ← Functor.map_comp_apply,
    ← op_comp] at this
  exact this

variable {D} in
lemma IsDelta.unique {T : Over S} {x y : D.P.obj (op T)}
    (hxy : D.π.app (op T) x = D.π.app (op T) y) {d d' : T ⟶ D.Q.X}
    (hd : D.IsDelta x y d) (hd' : D.IsDelta x y d') : d = d' := by
  obtain ⟨R, hR, hRx⟩ := D.locally_orbit x y hxy
  apply D.ext_of_mem hR
  intro V g hg
  obtain ⟨h, hh⟩ := hRx g hg
  rw [hd g h hh, hd' g h hh]

variable {D} in
lemma IsDelta.comp {T T' : Over S} {x y : D.P.obj (op T)} {d : T ⟶ D.Q.X}
    (hd : D.IsDelta x y d) (a : T' ⟶ T) :
    D.IsDelta (D.P.map a.op x) (D.P.map a.op y) (a ≫ d) := by
  intro V g h hh
  rw [← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp] at hh
  rw [← Category.assoc]
  exact hd (g ≫ a) h hh

lemma isDelta_act_self {T : Over S} (h : T ⟶ D.H.X) (y : D.P.obj (op T)) :
    D.IsDelta (D.act h y) y (h ≫ D.q.hom.hom) := by
  intro V g k hk
  rw [D.map_act] at hk
  rw [← Category.assoc]
  exact D.comp_q_eq_of_act_eq hk

variable {D} in
lemma IsDelta.act {T : Over S} {x y : D.P.obj (op T)} {d : T ⟶ D.Q.X}
    (hd : D.IsDelta x y d) (h h' : T ⟶ D.H.X) :
    D.IsDelta (D.act h x) (D.act h' y)
      ((h ≫ D.q.hom.hom) * d * (h' ≫ D.q.hom.hom)⁻¹) := by
  intro V g k hk
  rw [D.map_act, D.map_act] at hk
  have hk' : D.P.map g.op x = D.act ((g ≫ h)⁻¹ * k * (g ≫ h')) (D.P.map g.op y) := by
    rw [D.act_mul, D.act_mul, ← hk, act_inv_act]
  have e := hd g _ hk'
  rw [MonObj.comp_mul, MonObj.comp_mul, GrpObj.comp_inv, e, MonObj.mul_comp, MonObj.mul_comp,
    GrpObj.inv_comp, ← Category.assoc, ← Category.assoc]
  group

variable {D} in
lemma IsDelta.mul {T : Over S} {x y z : D.P.obj (op T)} {d e : T ⟶ D.Q.X}
    (hyz : D.π.app (op T) y = D.π.app (op T) z)
    (hd : D.IsDelta x y d) (he : D.IsDelta y z e) : D.IsDelta x z (d * e) := by
  intro V g h hh
  have hyz' : D.π.app (op V) (D.P.map g.op y) = D.π.app (op V) (D.P.map g.op z) := by
    rw [NatTrans.naturality_apply, NatTrans.naturality_apply, hyz]
  obtain ⟨R, hR, hRx⟩ := D.locally_orbit _ _ hyz'
  apply D.ext_of_mem hR
  intro W a ha
  obtain ⟨k, hk⟩ := hRx a ha
  rw [← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp] at hk
  have hx : D.P.map (a ≫ g).op x = D.act ((a ≫ h) * k⁻¹) (D.P.map (a ≫ g).op y) := by
    have := congrArg (D.P.map a.op) hh
    rw [D.map_act, ← Functor.map_comp_apply, ← Functor.map_comp_apply,
      ← op_comp] at this
    rw [this, hk, D.act_mul, act_inv_act]
  have e₁ := hd (a ≫ g) _ hx
  have e₂ := he (a ≫ g) _ hk
  have key : (a ≫ g) ≫ (d * e) = (a ≫ h) ≫ D.q.hom.hom := by
    rw [MonObj.comp_mul, e₁, e₂, MonObj.mul_comp, GrpObj.inv_comp]
    group
  simpa only [Category.assoc] using key

variable {D} in
/-- A section whose difference with `y` is trivial agrees with `y`, when `P` is separated. -/
lemma IsDelta.eq_of_one (hP : Presieve.IsSeparated (fppfTopology S) D.P)
    {T : Over S} {x y : D.P.obj (op T)}
    (hxy : D.π.app (op T) x = D.π.app (op T) y) (hd : D.IsDelta x y 1) : x = y := by
  obtain ⟨R, hR, hRx⟩ := D.locally_orbit x y hxy
  apply (hP R hR).ext
  intro V g hg
  obtain ⟨h, hh⟩ := hRx g hg
  have e := hd g h hh
  rw [MonObj.comp_one] at e
  rw [hh]
  exact (D.act_eq_self_iff h _).mpr e.symm

lemma isDelta_self {T : Over S} (y : D.P.obj (op T)) : D.IsDelta y y 1 := by
  intro V g h hh
  rw [MonObj.comp_one]
  exact ((D.act_eq_self_iff h _).mp hh.symm).symm

lemma isDelta_self_act {T : Over S} (h : T ⟶ D.H.X) (y : D.P.obj (op T)) :
    D.IsDelta y (D.act h y) (h ≫ D.q.hom.hom)⁻¹ := by
  intro V g k hk
  rw [D.map_act, ← D.act_mul] at hk
  have e : (1 : V ⟶ D.H.X) ≫ D.q.hom.hom = (k * (g ≫ h)) ≫ D.q.hom.hom :=
    D.comp_q_eq_of_act_eq (x := D.P.map g.op y) (by rw [D.act_one]; exact hk)
  rw [MonObj.one_comp, MonObj.mul_comp] at e
  rw [GrpObj.comp_inv, ← Category.assoc]
  exact (eq_inv_of_mul_eq_one_left e.symm).symm

lemma π_map_eq {T T' : Over S} {x y : D.P.obj (op T)}
    (hxy : D.π.app (op T) x = D.π.app (op T) y) (a : T' ⟶ T) :
    D.π.app (op T') (D.P.map a.op x) = D.π.app (op T') (D.P.map a.op y) := by
  rw [NatTrans.naturality_apply, NatTrans.naturality_apply, hxy]

/-- If the homomorphism `q` is smooth and surjective, sections of `P` with the same image
in `E` are translates of each other etale-locally. -/
theorem etale_locally_orbit (hP : Presieve.IsSeparated (fppfTopology S) D.P)
    [Smooth D.q.hom.hom.left] [Surjective D.q.hom.hom.left]
    {T : Over S} (x y : D.P.obj (op T)) (hxy : D.π.app (op T) x = D.π.app (op T) y) :
    ∃ R ∈ Scheme.etaleTopology.over S T, ∀ ⦃V : Over S⦄ (g : V ⟶ T), R g →
      ∃ h : V ⟶ D.H.X, D.P.map g.op x = D.act h (D.P.map g.op y) := by
  obtain ⟨d, hd⟩ := D.exists_isDelta hxy
  obtain ⟨V, e, s, he, hes, hs⟩ := smoothSurjectiveEtaleLocalSections _ _
    (pullback.snd D.q.hom.hom.left d.left) inferInstance inferInstance
  let V' : Over S := Over.mk (e ≫ T.hom)
  let g : V' ⟶ T := Over.homMk e
  have hfst : s ≫ pullback.fst D.q.hom.hom.left d.left ≫ D.q.hom.hom.left = e ≫ d.left := by
    rw [pullback.condition, ← Category.assoc, hs]
  let h : V' ⟶ D.H.X := Over.homMk (s ≫ pullback.fst D.q.hom.hom.left d.left) (by
    change (s ≫ pullback.fst D.q.hom.hom.left d.left) ≫ D.H.X.hom = e ≫ T.hom
    rw [← Over.w D.q.hom.hom, ← Category.assoc, Category.assoc s, hfst, Category.assoc,
      Over.w d])
  have hgq : h ≫ D.q.hom.hom = g ≫ d := by
    ext
    change (s ≫ pullback.fst D.q.hom.hom.left d.left) ≫ D.q.hom.hom.left = e ≫ d.left
    rw [Category.assoc]
    exact hfst
  have : Etale g.left := he
  have : Surjective g.left := hes
  have key : D.P.map g.op x = D.act h (D.P.map g.op y) := by
    have h₁ := (hd.comp g).mul (D.π_act h _).symm (D.isDelta_self_act h (D.P.map g.op y))
    rw [← hgq, mul_inv_cancel] at h₁
    refine h₁.eq_of_one hP ?_
    rw [D.π_act]
    exact D.π_map_eq hxy g
  refine ⟨Sieve.generate (Presieve.singleton g), generate_singleton_mem_etaleTopology g, ?_⟩
  rintro W _ ⟨Z, a, _, ⟨⟩, rfl⟩
  refine ⟨a ≫ h, ?_⟩
  rw [op_comp, Functor.map_comp_apply, Functor.map_comp_apply, key, D.map_act]

variable {D} in
lemma IsDelta.comp' {T T' : Over S} {U : Over S} {p : D.P.obj (op U)} {a b : T ⟶ U}
    {d : T ⟶ D.Q.X} (hd : D.IsDelta (D.P.map a.op p) (D.P.map b.op p) d) (c : T' ⟶ T) :
    D.IsDelta (D.P.map (c ≫ a).op p) (D.P.map (c ≫ b).op p) (c ≫ d) := by
  simpa only [op_comp, Functor.map_comp_apply] using hd.comp c

end QuotientAction

/-- A sieve containing, through every point, an etale map is an etale covering sieve. -/
lemma etale_mem_of_points {S : Scheme.{u}} {T : Over S} (R : Sieve T)
    (h : ∀ t : T.left, ∃ (V : Over S) (g : V ⟶ T), R g ∧ Etale g.left ∧ t ∈ Set.range g.left) :
    R ∈ Scheme.etaleTopology.over S T := by
  choose V g hR he ht using h
  let 𝒰 := Scheme.Cover.mkOfCovers (P := @Etale) T.left (fun t ↦ (V t).left)
    (fun t ↦ (g t).left) (fun t ↦ ⟨t, ht t⟩) (fun t ↦ he t)
  have hmem : Sieve.ofArrows V g ∈ Scheme.etaleTopology.over S T := by
    rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
    exact 𝒰.mem_grothendieckTopology
  refine (Scheme.etaleTopology.over S).superset_covering ?_ hmem
  rw [Sieve.ofArrows, Sieve.generate_le_iff]
  rintro _ _ ⟨t⟩
  exact hR t

/-- An fppf covering sieve contains, through every point, a flat finitely presented
surjection between affine schemes over an affine open. -/
lemma exists_affine_chart {S : Scheme.{u}} {T : Over S} {R : Sieve T}
    (hR : R ∈ fppfTopology S T) (t : T.left) :
    ∃ (W U : Over S) (incl : W ⟶ T) (r : U ⟶ W), IsAffine W.left ∧ IsAffine U.left ∧
      Flat r.left ∧ LocallyOfFinitePresentation r.left ∧ Surjective r.left ∧
      IsOpenImmersion incl.left ∧ R (r ≫ incl) ∧ t ∈ Set.range incl.left := by
  obtain ⟨Dop, V0, g0, g0', hD, hV0, hflat, hlfp, hcomp, hJ, ht⟩ :=
    LocallyQuasiFiniteDescent.exists_affineChart hR t
  have hg0flat : Flat g0.left := by rw [← hcomp]; infer_instance
  have hg0lfp : LocallyOfFinitePresentation g0.left := by rw [← hcomp]; infer_instance
  have htD : t ∈ Dop := by
    obtain ⟨t0, rfl⟩ := ht
    rw [← hcomp]
    exact (g0' t0).2
  let O : T.left.Opens := ⟨Set.range g0.left, g0.left.isOpenMap.isOpen_range⟩
  obtain ⟨f, hfO, htf⟩ := hD.exists_basicOpen_le (V := O) ⟨t, ht⟩ htD
  let Wo := T.left.basicOpen f
  have hWo : IsAffineOpen Wo := hD.basicOpen f
  have htop : g0.left ⁻¹ᵁ Dop = ⊤ := by
    rw [eq_top_iff]
    intro x _
    change g0.left x ∈ Dop
    rw [← hcomp]
    exact (g0' x).2
  have hpre : IsAffineOpen (g0.left ⁻¹ᵁ Dop) := by
    rw [htop]
    exact isAffineOpen_top V0.left
  let Uo := g0.left ⁻¹ᵁ Wo
  have hUo : IsAffineOpen Uo := by
    change IsAffineOpen (g0.left ⁻¹ᵁ T.left.basicOpen f)
    rw [Scheme.preimage_basicOpen]
    exact hpre.basicOpen _
  let W : Over S := Over.mk (Wo.ι ≫ T.hom)
  let incl : W ⟶ T := Over.homMk Wo.ι
  let U : Over S := Over.mk (Uo.ι ≫ V0.hom)
  let r : U ⟶ W := Over.homMk (g0.left ∣_ Wo) (by
    change (g0.left ∣_ Wo) ≫ Wo.ι ≫ T.hom = Uo.ι ≫ V0.hom
    rw [← Category.assoc, morphismRestrict_ι, Category.assoc, Over.w g0])
  have hrι : r ≫ incl = (Over.homMk Uo.ι rfl : U ⟶ V0) ≫ g0 := by
    ext
    exact morphismRestrict_ι g0.left Wo
  have : Flat (g0.left ∣_ Wo) := inferInstance
  have : LocallyOfFinitePresentation (g0.left ∣_ Wo) := inferInstance
  refine ⟨W, U, incl, r, hWo, hUo, inferInstanceAs (Flat (g0.left ∣_ Wo)),
    inferInstanceAs (LocallyOfFinitePresentation (g0.left ∣_ Wo)), ⟨fun y ↦ ?_⟩,
    inferInstanceAs (IsOpenImmersion Wo.ι), ?_, ⟨⟨t, htf⟩, rfl⟩⟩
  · have hy : Wo.ι y ∈ Wo := y.2
    obtain ⟨v, hv⟩ : (Wo.ι y) ∈ Set.range g0.left := hfO hy
    have hvU : v ∈ Uo := by
      change g0.left v ∈ Wo
      rw [hv]
      exact hy
    refine ⟨(⟨v, hvU⟩ : Uo.toScheme), Wo.ι.isOpenEmbedding.injective ?_⟩
    change (g0.left ∣_ Wo ≫ Wo.ι) (⟨v, hvU⟩ : Uo.toScheme) = Wo.ι y
    rw [morphismRestrict_ι]
    exact hv
  · rw [hrι]
    exact R.downward_closed hJ _

section Separated

variable {S : Scheme.{u}}

/-- A single flat surjective quasi-compact morphism generates a covering sieve in the slice
fpqc topology. -/
lemma generate_singleton_mem_fpqcTopology {W M : Over S} (q : W ⟶ M)
    [Flat q.left] [Surjective q.left] [QuasiCompact q.left] :
    Sieve.generate (Presieve.singleton q) ∈ Scheme.fpqcTopology.over S M := by
  change Sieve.overEquiv M (Sieve.generate (Presieve.singleton q)) ∈
    Scheme.fpqcTopology M.left
  rw [← Presieve.ofArrows_pUnit.{0} q, ← Sieve.ofArrows,
    Sieve.overEquiv_ofArrows, Sieve.ofArrows, Presieve.ofArrows_pUnit]
  exact Precoverage.generate_mem_toGrothendieck q.left.singleton_mem_fpqcPrecoverage

/-- The subpresheaf of the points of `T` along which two sections of `P` agree. -/
def agreement (P : (Over S)ᵒᵖ ⥤ Type (u + 1)) {T : Over S} (x y : P.obj (op T)) :
    (Over S)ᵒᵖ ⥤ Type u where
  obj V := {g : V.unop ⟶ T // P.map g.op x = P.map g.op y}
  map a := TypeCat.ofHom (fun g ↦ ⟨a.unop ≫ g.1, by
    rw [op_comp, Functor.map_comp_apply, Functor.map_comp_apply, g.2]⟩)
  map_id V := by
    ext g
    simp
  map_comp a b := by
    ext g
    simp

lemma agreement_map_val (P : (Over S)ᵒᵖ ⥤ Type (u + 1)) {T : Over S} (x y : P.obj (op T))
    {V W : Over S} (a : W ⟶ V) (g : (agreement P x y).obj (op V)) :
    ((agreement P x y).map a.op g).1 = a ≫ g.1 :=
  rfl

/-- **Separation criterion.** A presheaf on the slice of schemes which is separated for the
Zariski topology and for every single affine faithfully flat morphism is separated for the
fppf topology. -/
theorem isSeparated_fppf_of_zariski_of_affine (P : (Over S)ᵒᵖ ⥤ Type (u + 1))
    (hzar : Presieve.IsSeparated (Scheme.zariskiTopology.over S) P)
    (haff : ∀ {R R' : CommRingCat.{u}} (φ : R ⟶ R'), Flat (Spec.map φ) →
      Surjective (Spec.map φ) → ∀ s : Spec R ⟶ S, Presieve.IsSeparatedFor P
        (.singleton (Over.homMk (Spec.map φ) : Over.mk (Spec.map φ ≫ s) ⟶ Over.mk s))) :
    Presieve.IsSeparated (fppfTopology S) P := by
  intro T R hR famP x y hx hy
  have hxy : ∀ ⦃V : Over S⦄ (g : V ⟶ T), R g → P.map g.op x = P.map g.op y :=
    fun V g hg ↦ (hx g hg).trans (hy g hg).symm
  have hG : Presieve.IsSheaf (Scheme.fppfTopology.over S) (agreement P x y) := by
    apply OverFppfSheaf.isSheaf_fppfTopology_over
    · intro V R' hR' fam hfam
      have hY := GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable
        (J := Scheme.zariskiTopology.over S) (yoneda.obj T)
      let famY : Presieve.FamilyOfElements (yoneda.obj T) R'.arrows :=
        fun W g hg ↦ (fam g hg).1
      have hcY : famY.Compatible := by
        intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ w
        have := congrArg Subtype.val (hfam g₁ g₂ h₁ h₂ w)
        rw [agreement_map_val, agreement_map_val] at this
        exact this
      obtain ⟨g, hg, hgu⟩ := hY R' hR' famY hcY
      have hg' : ∀ ⦃W : Over S⦄ (f : W ⟶ V) (hf : R' f), f ≫ g = (fam f hf).1 :=
        fun W f hf ↦ hg f hf
      have hgP : P.map g.op x = P.map g.op y := by
        apply (hzar R' hR').ext
        intro W f hf
        rw [← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp, hg' f hf]
        exact (fam f hf).2
      refine ⟨⟨g, hgP⟩, fun W f hf ↦ Subtype.ext (hg' f hf), fun g' hg'' ↦ Subtype.ext ?_⟩
      exact hgu g'.1 (fun W f hf ↦ by
        have := congrArg Subtype.val (hg'' f hf)
        rw [agreement_map_val] at this
        exact this)
    · intro R₀ R₁ φ hf hs s₀
      have : Flat (Spec.map φ) := hf
      have : Surjective (Spec.map φ) := hs
      let m : Over.mk (Spec.map φ ≫ s₀) ⟶ Over.mk s₀ := Over.homMk (Spec.map φ)
      have : Flat m.left := hf
      have : Surjective m.left := hs
      have : QuasiCompact m.left := inferInstanceAs (QuasiCompact (Spec.map φ))
      have hY := (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable
        (J := Scheme.fpqcTopology.over S) (yoneda.obj T)) _
        (generate_singleton_mem_fpqcTopology m)
      rw [← Presieve.isSheafFor_iff_generate] at hY
      intro fam hfam
      let famY : Presieve.FamilyOfElements (yoneda.obj T) (Presieve.singleton m) :=
        fun W g hg ↦ (fam g hg).1
      have hcY : famY.Compatible := by
        intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ w
        have := congrArg Subtype.val (hfam g₁ g₂ h₁ h₂ w)
        rw [agreement_map_val, agreement_map_val] at this
        exact this
      obtain ⟨g, hg, hgu⟩ := hY famY hcY
      have hg' : m ≫ g = (fam m Presieve.singleton.mk).1 := hg m Presieve.singleton.mk
      have hgP : P.map g.op x = P.map g.op y := by
        apply (haff φ hf hs s₀).ext
        rintro W _ ⟨⟩
        rw [← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp]
        change P.map (m ≫ g).op x = P.map (m ≫ g).op y
        rw [hg']
        exact (fam m _).2
      refine ⟨⟨g, hgP⟩, fun W f hf ↦ Subtype.ext (hg f hf), fun g' hg'' ↦ Subtype.ext ?_⟩
      exact hgu g'.1 (fun W f hf ↦ by
        have := congrArg Subtype.val (hg'' f hf)
        rw [agreement_map_val] at this
        exact this)
  let fam : Presieve.FamilyOfElements (agreement P x y) R.arrows :=
    fun V g hg ↦ ⟨g, hxy g hg⟩
  have hc : fam.Compatible := by
    intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ w
    apply Subtype.ext
    rw [agreement_map_val, agreement_map_val]
    exact w
  obtain ⟨⟨g₀, hg₀⟩, hamal⟩ := (hG R hR fam hc).exists
  have hY := GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable
    (J := fppfTopology S) (yoneda.obj T)
  have h₀ : g₀ = 𝟙 T := by
    apply (hY.isSeparated R hR).ext
    intro V f hf
    have := congrArg Subtype.val (hamal f hf)
    rw [agreement_map_val] at this
    change f ≫ g₀ = f ≫ 𝟙 T
    rw [this, Category.comp_id]
  subst h₀
  simpa using hg₀

end Separated

namespace QuotientAction

variable {S : Scheme.{u}} (D : QuotientAction S)

section Cocycle

variable {W U : Over S} (r : U ⟶ W)

lemma lift_w {Z : Over W.left} (a : Z ⟶ Over.mk r.left) :
    a.left ≫ U.hom = ((Over.map W.hom).obj Z).hom := by
  have h := Over.w a
  simp only [Over.mk_hom] at h
  simp only [Over.map_obj_hom]
  rw [← h, Category.assoc, Over.w r]

/-- A map to the cover over `W`, read as a map of schemes over `S`. -/
def liftHom {Z : Over W.left} (a : Z ⟶ Over.mk r.left) : (Over.map W.hom).obj Z ⟶ U :=
  Over.homMk a.left (lift_w r a)

@[simp]
lemma liftHom_left {Z : Over W.left} (a : Z ⟶ Over.mk r.left) : (liftHom r a).left = a.left :=
  rfl

lemma liftHom_comp {Z Z' : Over W.left} (t : Z' ⟶ Z) (a : Z ⟶ Over.mk r.left) :
    liftHom r (t ≫ a) = (Over.map W.hom).map t ≫ liftHom r a := by
  ext
  rfl

lemma liftHom_comp_r {Z : Over W.left} (a b : Z ⟶ Over.mk r.left) :
    liftHom r a ≫ r = liftHom r b ≫ r := by
  ext
  have ha := Over.w a
  have hb := Over.w b
  simp only [Over.mk_hom] at ha hb
  change a.left ≫ r.left = b.left ≫ r.left
  rw [ha, hb]

variable (p : D.P.obj (op U))
  (hπ : ∀ ⦃Z : Over S⦄ (a b : Z ⟶ U), a ≫ r = b ≫ r →
    D.π.app (op Z) (D.P.map a.op p) = D.π.app (op Z) (D.P.map b.op p))

include hπ in
lemma exists_isDelta_lift {Z : Over W.left} (a b : Z ⟶ Over.mk r.left) :
    ∃ d, D.IsDelta (D.P.map (liftHom r a).op p) (D.P.map (liftHom r b).op p) d :=
  D.exists_isDelta (hπ _ _ (liftHom_comp_r r a b))

/-- The chosen `Q`-valued difference of the two pullbacks of `p`. -/
def liftDelta {Z : Over W.left} (a b : Z ⟶ Over.mk r.left) :
    (Over.map W.hom).obj Z ⟶ D.Q.X :=
  (D.exists_isDelta_lift r p hπ a b).choose

lemma liftDelta_spec {Z : Over W.left} (a b : Z ⟶ Over.mk r.left) :
    D.IsDelta (D.P.map (liftHom r a).op p) (D.P.map (liftHom r b).op p)
      (D.liftDelta r p hπ a b) :=
  (D.exists_isDelta_lift r p hπ a b).choose_spec

lemma liftDelta_eq {Z : Over W.left} (a b : Z ⟶ Over.mk r.left) {d}
    (hd : D.IsDelta (D.P.map (liftHom r a).op p) (D.P.map (liftHom r b).op p) d) :
    D.liftDelta r p hπ a b = d :=
  IsDelta.unique (hπ _ _ (liftHom_comp_r r a b)) (D.liftDelta_spec r p hπ a b) hd

/-- The `Q`-valued cocycle of a section of `P` over an fppf cover, whose two pullbacks have
the same image in `E`. -/
def cocycle : Cocycle ((GroupScheme.baseChange W.hom).obj D.Q) (Over.mk r.left) where
  toFun {Z} a b := (baseChangePointsEquiv W.hom D.Q Z).symm (D.liftDelta r p hπ a b)
  naturality {Z Z'} t a b := by
    apply (baseChangePointsEquiv W.hom D.Q Z').injective
    rw [MulEquiv.apply_symm_apply, baseChangePointsEquiv_naturality, MulEquiv.apply_symm_apply]
    apply D.liftDelta_eq
    rw [liftHom_comp, liftHom_comp]
    exact (D.liftDelta_spec r p hπ a b).comp' _
  cocycle {Z} a b c := by
    apply (baseChangePointsEquiv W.hom D.Q Z).injective
    rw [map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
    apply D.liftDelta_eq
    exact (D.liftDelta_spec r p hπ a b).mul (hπ _ _ (liftHom_comp_r r b c))
      (D.liftDelta_spec r p hπ b c)

lemma cocycle_spec {Z : Over W.left} (a b : Z ⟶ Over.mk r.left) :
    D.IsDelta (D.P.map (liftHom r a).op p) (D.P.map (liftHom r b).op p)
      (baseChangePointsEquiv W.hom D.Q Z ((D.cocycle r p hπ).toFun a b)) := by
  change D.IsDelta _ _ ((baseChangePointsEquiv W.hom D.Q Z)
    ((baseChangePointsEquiv W.hom D.Q Z).symm (D.liftDelta r p hπ a b)))
  rw [MulEquiv.apply_symm_apply]
  exact D.liftDelta_spec r p hπ a b

end Cocycle

section Lift

variable [Smooth D.Q.X.hom] [IsAffineHom D.Q.X.hom]
  [Flat D.q.hom.hom.left] [Surjective D.q.hom.hom.left]
  [LocallyOfFinitePresentation D.q.hom.hom.left] [IsAffineHom D.q.hom.hom.left]

/-- **Etale-local lifts.** Over an affine `W`, a section of `E` which lifts to `P` along a flat
finitely presented surjection from an affine scheme lifts to `F` along an etale surjection,
provided descent data in `P` along fppf affine maps descend to sections of `F`. -/
theorem exists_etale_lift (hP : Presieve.IsSeparated (fppfTopology S) D.P)
    (hE : Presieve.IsSeparated (fppfTopology S) D.E)
    {F : (Over S)ᵒᵖ ⥤ Type (u + 1)} (toE : F ⟶ D.E)
    (hdesc : ∀ {U V : Over S} (m : U ⟶ V), IsAffineHom m.left → Flat m.left →
      Surjective m.left → LocallyOfFinitePresentation m.left → ∀ p : D.P.obj (op U),
      (∀ ⦃Z : Over S⦄ (a b : Z ⟶ U), a ≫ m = b ≫ m → D.P.map a.op p = D.P.map b.op p) →
        ∃ y : F.obj (op V), D.E.map m.op (toE.app (op V) y) = D.π.app (op U) p)
    {W U : Over S} [IsAffine W.left] [IsAffine U.left] (r : U ⟶ W)
    [Flat r.left] [Surjective r.left] [LocallyOfFinitePresentation r.left]
    (sW : D.E.obj (op W)) (p : D.P.obj (op U)) (hp : D.π.app (op U) p = D.E.map r.op sW) :
    ∃ (V : Over S) (e : V ⟶ W) (y : F.obj (op V)),
      Etale e.left ∧ Surjective e.left ∧ toE.app (op V) y = D.E.map e.op sW := by
  have hπ : ∀ ⦃Z : Over S⦄ (a b : Z ⟶ U), a ≫ r = b ≫ r →
      D.π.app (op Z) (D.P.map a.op p) = D.π.app (op Z) (D.P.map b.op p) := by
    intro Z a b hab
    rw [NatTrans.naturality_apply, NatTrans.naturality_apply, hp, ← Functor.map_comp_apply,
      ← Functor.map_comp_apply, ← op_comp, ← op_comp, hab]
  let ξ := D.cocycle r p hπ
  let QW := (GroupScheme.baseChange W.hom).obj D.Q
  let UW : Over W.left := Over.mk r.left
  have : IsAffineHom QW.X.hom := inferInstanceAs (IsAffineHom (pullback.snd D.Q.X.hom W.hom))
  have : Smooth QW.X.hom := inferInstanceAs (Smooth (pullback.snd D.Q.X.hom W.hom))
  have : IsAffine UW.left := inferInstanceAs (IsAffine U.left)
  have : Flat UW.hom := inferInstanceAs (Flat r.left)
  have : Surjective UW.hom := inferInstanceAs (Surjective r.left)
  let Y := CocycleTorsor.torsor ξ
  let := CocycleTorsor.modObj ξ
  have hY : IsIso (ModObj.leftSMul QW.X Y) := CocycleTorsor.isIso_leftSMul ξ
  obtain ⟨Vs, e, σ, he, hes, hσ⟩ := smoothSurjectiveEtaleLocalSections Y.left W.left Y.hom
    (CocycleTorsor.smooth_hom ξ) (CocycleTorsor.surjective_hom ξ)
  let pr1 := pullback.fst r.left e
  let pr2 := pullback.snd r.left e
  let VsW : Over W.left := Over.mk e
  let UeW : Over W.left := Over.mk (pr2 ≫ e)
  let prW1 : UeW ⟶ UW := Over.homMk pr1 pullback.condition
  let prW2 : UeW ⟶ VsW := Over.homMk pr2 rfl
  let σW : VsW ⟶ Y := Over.homMk σ hσ
  let x1 : UeW ⟶ Y := prW1 ≫ CocycleTorsor.point ξ
  let x2 : UeW ⟶ Y := prW2 ≫ σW
  let f := torsorDiff hY x2 x1
  have hf : f • x2 = x1 := torsorDiff_smul hY x2 x1
  have hcob : ∀ {Z : Over W.left} (a b : Z ⟶ UeW), a ≫ prW2 = b ≫ prW2 →
      ξ.toFun (a ≫ prW1) (b ≫ prW1) = (a ≫ f) * (b ≫ f)⁻¹ := by
    intro Z a b hab
    have h1 := CocycleTorsor.toFun_smul_point ξ (a ≫ prW1) (b ≫ prW1)
    have hx (c : Z ⟶ UeW) : (c ≫ prW1) ≫ CocycleTorsor.point ξ = (c ≫ f) • (c ≫ x2) := by
      rw [Category.assoc]
      change c ≫ x1 = _
      rw [← hf, ModObj.comp_smul]
    have hx2 : a ≫ x2 = b ≫ x2 := by
      change a ≫ prW2 ≫ σW = b ≫ prW2 ≫ σW
      rw [← Category.assoc, hab, Category.assoc]
    rw [hx a, hx b, ← hx2, smul_smul] at h1
    have e1 : ξ.toFun (a ≫ prW1) (b ≫ prW1) * (b ≫ f) = a ≫ f :=
      (eq_torsorDiff hY h1).trans (eq_torsorDiff hY rfl).symm
    rw [← e1, mul_inv_cancel_right]
  let f' := baseChangePointsEquiv W.hom D.Q UeW f
  let Ue : Over S := (Over.map W.hom).obj UeW
  let ρ := pullback.snd D.q.hom.hom.left f'.left
  let k := pullback.fst D.q.hom.hom.left f'.left
  let U' : Over S := Over.mk (ρ ≫ Ue.hom)
  let ρo : U' ⟶ Ue := Over.homMk ρ rfl
  let ko : U' ⟶ D.H.X := Over.homMk k (by
    change k ≫ D.H.X.hom = ρ ≫ Ue.hom
    rw [← Over.w D.q.hom.hom, ← Category.assoc, pullback.condition, Category.assoc, Over.w f'])
  have hk : ko ≫ D.q.hom.hom = ρo ≫ f' := by
    ext
    exact pullback.condition
  obtain ⟨c, hc⟩ : ∃ c : U' ⟶ U, c = ρo ≫ liftHom r prW1 := ⟨_, rfl⟩
  let V' : Over S := (Over.map W.hom).obj VsW
  obtain ⟨m, hm⟩ : ∃ m : U' ⟶ V', m = ρo ≫ (Over.map W.hom).map prW2 := ⟨_, rfl⟩
  let eV : V' ⟶ W := Over.homMk e rfl
  have hcr : c ≫ r = m ≫ eV := by
    rw [hc, hm]
    ext
    change ρ ≫ pr1 ≫ r.left = ρ ≫ pr2 ≫ e
    rw [pullback.condition]
  let p' := D.act ko⁻¹ (D.P.map c.op p)
  have hcompat : ∀ ⦃Z : Over S⦄ (a b : Z ⟶ U'), a ≫ m = b ≫ m →
      D.P.map a.op p' = D.P.map b.op p' := by
    intro Z a b hab
    have hab' : a.left ≫ ρ ≫ pr2 = b.left ≫ ρ ≫ pr2 := by
      rw [hm] at hab
      exact congrArg (fun g ↦ g.left) hab
    let ZW : Over W.left := Over.mk (a.left ≫ ρ ≫ pr2 ≫ e)
    let aW : ZW ⟶ UeW := Over.homMk (a.left ≫ ρ) (by simp [ZW, UeW])
    let bW : ZW ⟶ UeW := Over.homMk (b.left ≫ ρ) (by
      change (b.left ≫ ρ) ≫ pr2 ≫ e = a.left ≫ ρ ≫ pr2 ≫ e
      simp only [Category.assoc]
      rw [← Category.assoc ρ, ← Category.assoc b.left, ← hab']
      simp only [Category.assoc])
    have habW : aW ≫ prW2 = bW ≫ prW2 := by
      ext
      change (a.left ≫ ρ) ≫ pr2 = (b.left ≫ ρ) ≫ pr2
      simpa only [Category.assoc] using hab'
    have hc' := congrArg (baseChangePointsEquiv W.hom D.Q ZW) (hcob aW bW habW)
    rw [map_mul, map_inv, baseChangePointsEquiv_naturality,
      baseChangePointsEquiv_naturality] at hc'
    have hspec := D.cocycle_spec r p hπ (aW ≫ prW1) (bW ≫ prW1)
    rw [hc'] at hspec
    let ε : Z ⟶ (Over.map W.hom).obj ZW := Over.homMk (𝟙 Z.left) (by
      have := Over.w a
      simp only [ZW, U', Ue, UeW, Over.map_obj_hom, Over.mk_hom] at this ⊢
      rw [← this]
      simp only [Category.id_comp, Category.assoc])
    have hεa : ε ≫ liftHom r (aW ≫ prW1) = a ≫ c := by
      rw [hc]
      ext
      simp [ε, aW, prW1, ρo, liftHom]
    have hεb : ε ≫ liftHom r (bW ≫ prW1) = b ≫ c := by
      rw [hc]
      ext
      simp [ε, bW, prW1, ρo, liftHom]
    have hεfa : ε ≫ (Over.map W.hom).map aW ≫ f' = a ≫ ko ≫ D.q.hom.hom := by
      rw [hk]
      ext
      simp [ε, aW, ρo]
    have hεfb : ε ≫ (Over.map W.hom).map bW ≫ f' = b ≫ ko ≫ D.q.hom.hom := by
      rw [hk]
      ext
      simp [ε, bW, ρo]
    have hδ := hspec.comp' ε
    rw [hεa, hεb, MonObj.comp_mul, GrpObj.comp_inv, hεfa, hεfb] at hδ
    have hδ2 := hδ.act (a ≫ ko⁻¹) (b ≫ ko⁻¹)
    have h1 : ((a ≫ ko⁻¹) ≫ D.q.hom.hom) *
        ((a ≫ ko ≫ D.q.hom.hom) * (b ≫ ko ≫ D.q.hom.hom)⁻¹) *
          ((b ≫ ko⁻¹) ≫ D.q.hom.hom)⁻¹ = 1 := by
      rw [Category.assoc, Category.assoc, GrpObj.inv_comp, GrpObj.comp_inv, GrpObj.comp_inv]
      group
    rw [h1] at hδ2
    have ea : D.P.map a.op p' = D.act (a ≫ ko⁻¹) (D.P.map (a ≫ c).op p) := by
      change D.P.map a.op (D.act ko⁻¹ (D.P.map c.op p)) = _
      rw [D.map_act, ← Functor.map_comp_apply, ← op_comp]
    have eb : D.P.map b.op p' = D.act (b ≫ ko⁻¹) (D.P.map (b ≫ c).op p) := by
      change D.P.map b.op (D.act ko⁻¹ (D.P.map c.op p)) = _
      rw [D.map_act, ← Functor.map_comp_apply, ← op_comp]
    rw [ea, eb]
    apply hδ2.eq_of_one hP
    rw [D.π_act, D.π_act]
    apply hπ
    calc (a ≫ c) ≫ r = (a ≫ m) ≫ eV := by rw [Category.assoc, hcr, Category.assoc]
      _ = (b ≫ m) ≫ eV := by rw [hab]
      _ = (b ≫ c) ≫ r := by rw [Category.assoc, ← hcr, Category.assoc]
  have hmleft : m.left = ρ ≫ pr2 := by rw [hm]; rfl
  have : IsAffineHom r.left := inferInstance
  have : IsAffineHom pr2 := MorphismProperty.pullback_snd _ _ (inferInstance : IsAffineHom r.left)
  have : IsAffineHom ρ :=
    MorphismProperty.pullback_snd _ _ (inferInstance : IsAffineHom D.q.hom.hom.left)
  have hmaff : IsAffineHom m.left := by
    rw [hmleft]
    infer_instance
  have hmflat : Flat m.left := by
    rw [hmleft]
    infer_instance
  have hmsurj : Surjective m.left := by
    rw [hmleft]
    infer_instance
  have hmlfp : LocallyOfFinitePresentation m.left := by
    rw [hmleft]
    infer_instance
  obtain ⟨y, hy⟩ := hdesc m hmaff hmflat hmsurj hmlfp p' hcompat
  refine ⟨V', eV, y, he, hes, ?_⟩
  have key : D.E.map m.op (toE.app _ y) = D.E.map m.op (D.E.map eV.op sW) := by
    rw [hy]
    change D.π.app _ (D.act ko⁻¹ (D.P.map c.op p)) = _
    rw [D.π_act, NatTrans.naturality_apply, hp, ← Functor.map_comp_apply,
      ← Functor.map_comp_apply, ← op_comp, ← op_comp, hcr]
  apply (hE _ (generate_singleton_mem_fppfTopology m)).ext
  rintro Z _ ⟨Z', a, _, ⟨⟩, rfl⟩
  rw [op_comp, Functor.map_comp_apply, Functor.map_comp_apply, key]

/-- **Etale-local surjectivity.** If `P` and `E` are fppf separated, `π` is fppf-locally
surjective, and descent data in `P` along fppf affine maps descend to sections of `F`, then
`toE : F ⟶ E` is etale-locally surjective. -/
theorem isLocallySurjective_etale (hP : Presieve.IsSeparated (fppfTopology S) D.P)
    (hE : Presieve.IsSeparated (fppfTopology S) D.E)
    {F : (Over S)ᵒᵖ ⥤ Type (u + 1)} (toE : F ⟶ D.E)
    (hdesc : ∀ {U V : Over S} (m : U ⟶ V), IsAffineHom m.left → Flat m.left →
      Surjective m.left → LocallyOfFinitePresentation m.left → ∀ p : D.P.obj (op U),
      (∀ ⦃Z : Over S⦄ (a b : Z ⟶ U), a ≫ m = b ≫ m → D.P.map a.op p = D.P.map b.op p) →
        ∃ y : F.obj (op V), D.E.map m.op (toE.app (op V) y) = D.π.app (op U) p)
    (hπ : Presheaf.IsLocallySurjective (fppfTopology S) D.π) :
    Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) toE := by
  constructor
  intro T s
  apply etale_mem_of_points
  intro t
  obtain ⟨W, U, incl, r, hW, hU, hfl, hlfp, hsurj, hincl, hR, ht⟩ :=
    exists_affine_chart (Presheaf.imageSieve_mem (fppfTopology S) D.π s) t
  obtain ⟨p, hp⟩ := hR
  have hp' : D.π.app _ p = D.E.map r.op (D.E.map incl.op s) := by
    rw [hp, op_comp, Functor.map_comp_apply]
  obtain ⟨V, e, y, he, hes, hy⟩ := D.exists_etale_lift hP hE toE hdesc r _ p hp'
  refine ⟨V, e ≫ incl, ⟨y, ?_⟩, ?_, ?_⟩
  · rw [hy, op_comp, Functor.map_comp_apply]
  · change Etale (e.left ≫ incl.left)
    infer_instance
  · obtain ⟨w, rfl⟩ := ht
    obtain ⟨v, rfl⟩ := hes.surj w
    exact ⟨v, rfl⟩

end Lift

end QuotientAction

end Langlands.AlgebraicGeometry.Picard.QuotientActionLocality
