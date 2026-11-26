# A chosen common geometric point field

`CommonPointField X` packages a complete algebraically closed ultrametric extension of the ground field and surjectivity of its field-point projection onto the underlying space of `X`. `chooseCommonPointField X` makes such a choice using `commonAlgebraicallyClosedPointField`. Its carrier and field instances can be used directly in the geometric point and compact-support functors. The construction permits an independent universe parameter beyond the size of the analytic category.

Berkovich, *Étale equivariant sheaves on p-adic analytic spaces*, §1.5 p. 10, chooses a geometric point above each underlying point to construct Godement terms. Using a single extension field is a derived construction. It uses the Library's common-field theorem and the actual field-valued point projection.
