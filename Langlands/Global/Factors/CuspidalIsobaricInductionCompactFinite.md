# The compact action on the cuspidal induction tensor

`sourceCompactAction` is the full infinite compact action on the source
of `targetTensorAction_subquotient`. It uses the original-order real and
complex standard modules and the same finite tensor carrier and
references. `sourceCompactAction_finite_semisimple` proves every vector
is compact-finite and the action is semisimple over the group algebra.

The Library's real and complex standard module theorems provide local
compact finiteness and continuous coefficients. Apply the finite tensor
lemma to these factors, then use `KFiniteDual.isSemisimpleModule`, which
averages finite-dimensional compact representations. This is the
compact representation input to the projected specialization of
Langlands, *On the notion of an automorphic representation* (1979),
Lemma 7, printed pp. 205–206 (Corvallis Part I PDF pp. 200–201).
